//! Simulating and execution for LC-3 assembly.
//! 
//! This module is focused on executing fully assembled code (i.e., [`ObjectFile`]).
//! 
//! This module consists of:
//! - [`Simulator`]: The struct that simulates assembled code.
//! - [`mem`]: The module handling memory relating to the registers.
//! - [`SimIO`]: The struct handling the simulator's IO.

pub mod mem;
mod io;
pub mod debug;

use std::sync::atomic::AtomicBool;
use std::sync::Arc;

use crate::asm::ObjectFile;
use crate::ast::reg_consts::{R6, R7};
use crate::ast::sim::SimInstr;
use crate::ast::ImmOrReg;
pub use io::*;

use self::debug::Breakpoint;
use self::mem::{AssertInit as _, Mem, MemAccessCtx, RegFile, Word};

/// Errors that can occur during simulation.
#[derive(Debug)]
pub enum SimErr {
    /// Word was decoded, but the opcode was invalid.
    InvalidOpcode,
    /// Word was decoded, and the opcode is recognized,
    /// but the instruction's format is invalid.
    InvalidInstrFormat,
    /// A privileged instruction was called in user mode.
    PrivilegeViolation,
    /// A supervisor region was accessed in user mode.
    AccessViolation,
    /// Not an error, but HALT!
    ProgramHalted,
    /// A register was loaded with a partially uninitialized value.
    /// 
    /// This will ignore loads from the stack (R6), because it is convention to push registers 
    /// (including uninitialized registers).
    /// This also ignores loads from allocated (`.blkw`) memory in case the program writer
    /// uses those as register stores.

    // IDEA: So currently, the way this is implemented is that LDR Rx, R6, OFF is accepted regardless of initialization.
    // We could make this stricter by keeping track of how much is allocated on the stack.
    StrictRegSetUninit,
    /// Memory was loaded with a partially uninitialized value.
    /// 
    /// This will ignore loads from the stack (R6), because it is convention to push registers 
    /// (including uninitialized registers).
    /// This also ignores loads from allocated (`.blkw`) memory in case the program writer
    /// uses those as register stores.

    // IDEA: See StrictRegSetUninit.
    StrictMemSetUninit,
    /// Data was stored into MMIO with a partially uninitialized value.
    StrictIOSetUninit,
    /// Address to jump to is coming from an uninitialized value.
    StrictJmpAddrUninit,
    /// Address to read from memory is coming from an uninitialized value.
    StrictMemAddrUninit,
    /// PC is pointing to an uninitialized value.
    StrictPCMemUninit,
    /// The PSR was loaded with a partially uninitialized value (by RTI).
    StrictPSRSetUninit,
}

/// Executes assembled code.
#[derive(Debug)]
pub struct Simulator {
    /// The simulator's memory.
    /// 
    /// Note that this is held in the heap, as it is too large for the stack.
    pub mem: Mem,

    /// The simulator's register file.
    pub reg_file: RegFile,

    /// The program counter.
    pub pc: u16,

    /// The processor status register. See [`PSR`] for more details.
    psr: PSR,

    /// Saved stack pointer (the one currently not in use)
    saved_sp: Word,

    /// The number of subroutines or trap calls we've entered.
    /// 
    /// This is incremented when JSR/JSRR/TRAP is called,
    /// and decremented when RET/JMP R7/RTI is called.
    /// 
    /// If this is 0, this is considered the global state,
    /// and as such, decrementing should have no effect.
    /// 
    /// I am hoping this is large enough that it doesn't overflow :)
    sr_entered: u64,

    /// Whether strict mode is enabled.
    /// 
    /// Strict mode adds additional integrity checks to the simulator,
    /// such as verifying initialization state is normal for provided data.
    pub strict: bool,

    /// IO handler for the simulator.
    /// 
    /// This is an Option because it is only enabled when the OS is active.
    /// It is also an Option so that closing it (via [`Simulator::close_io`]) 
    /// does not require closing the entire Simulator.
    pub io: Option<io::SimIO>,

    /// Allocated blocks in object file.
    /// 
    /// Keeps track of allocated blocks in the current object file.
    /// Loading and setting to an allocated block does not 
    /// cause register/memory strictness errors.
    alloca: Box<[(u16, u16)]>,

    /// Machine control.
    /// If unset, the program stops.
    pub mcr: Arc<AtomicBool>,

    /// Any breakpoints to check for.
    pub breakpoints: Vec<Breakpoint>
}

impl Simulator {
    /// Creates a new simulator, without any object files loaded.
    pub fn new() -> Self {
        Self {
            mem: Mem::new(),
            reg_file: RegFile::new(),
            pc: 0x3000,
            psr: PSR::new(),
            saved_sp: Word::new_init(0x2FFF),
            sr_entered: 0,
            strict: false,
            io: None,
            alloca: Box::new([]),
            mcr: Arc::new(AtomicBool::new(false)),
            breakpoints: vec![]
        }
    }

    /// Loads and initializes the operating system (traps) and IO.
    /// 
    /// Even without the OS, the HALT trap can be used.
    pub fn load_os(&mut self) {
        use crate::parse::parse_ast;
        use crate::asm::assemble;

        self.io.replace(io::SimIO::new(Arc::clone(&self.mcr)));

        let os_file = include_str!("os.asm");
        let ast = parse_ast(os_file).unwrap();
        let obj = assemble(ast).unwrap();

        self.load_obj_file(&obj);
    }
    /// Closes the IO handler and awaits for the display to finish.
    pub fn close_io(&mut self) -> std::thread::Result<()> {
        let Some(io) = self.io.take() else { return Ok(()) } ;
        io.join()
    }
    
    /// Loads an object file into this simulator.
    pub fn load_obj_file(&mut self, obj: &ObjectFile) {
        use std::cmp::Ordering;

        let mut alloca = Vec::with_capacity(obj.len());

        for (start, words) in obj.iter() {
            self.mem.copy_block(start, words);

            // add this block to alloca
            let len = words.len() as u16;
            let end = start.wrapping_add(len);

            match start.cmp(&end) {
                Ordering::Less    => alloca.push((start, len)),
                Ordering::Equal   => {},
                Ordering::Greater => {
                    // push (start..) and (0..end) as blocks
                    alloca.push((start, start.wrapping_neg()));
                    if end != 0 { alloca.push((0, end)) };
                },
            }
        }

        alloca.sort_by_key(|&(start, _)| start);
        self.alloca = alloca.into_boxed_slice();
    }
    /// Wipes the simulator's state.
    pub fn clear(&mut self) {
        std::mem::take(self);
    }

    /// Sets the condition codes using the provided result.
    fn set_cc(&mut self, result: u16) {
        match (result as i16).cmp(&0) {
            std::cmp::Ordering::Less    => self.psr.set_cc(0b100),
            std::cmp::Ordering::Equal   => self.psr.set_cc(0b010),
            std::cmp::Ordering::Greater => self.psr.set_cc(0b001),
        }
    }

    /// Gets a reference to the PSR.
    pub fn psr(&self) -> &PSR {
        &self.psr
    }

    /// Sets the PC to the given address, raising any errors that occur.
    pub fn set_pc(&mut self, addr_word: Word) -> Result<(), SimErr> {
        let addr = addr_word.assert_init(self.strict, SimErr::StrictJmpAddrUninit)?.get();
        self.pc = addr;
        Ok(())
    }
    /// Adds an offset to the PC.
    pub fn offset_pc(&mut self, offset: i16) -> Result<(), SimErr> {
        self.set_pc(Word::from(self.pc.wrapping_add_signed(offset)))
    }

    /// Checks whether address is in allocated user space
    pub fn in_alloca(&self, addr: u16) -> bool {
        let first_post = self.alloca.partition_point(|&(start, _)| start <= addr);
        if first_post == 0 { return false };
        
        // This is the last block where start <= addr.
        let (start, len) = self.alloca[first_post - 1];

        // We must also check that addr < end.
        // If start + len is None, that means end is greater than all possible lengths.
        match start.checked_add(len) {
            Some(e) => addr < e,
            None    => true
        }
    }
    /// Computes the memory access context, 
    /// which are flags that control privilege and checks when accessing memory
    /// (see [`Mem::get`] and [`Mem::set`]).
    /// 
    /// Due to the way Rust lifetimes work, this does not automatically insert the IO device's
    /// reference.
    /// If you want to use this, try `self.mem_ctx(&self.io)` (or create a macro that does
    /// what this internally does).
    pub fn mem_ctx<'ctx>(&self, io: &'ctx Option<io::SimIO>) -> MemAccessCtx<'ctx> {
        MemAccessCtx { privileged: self.psr.privileged(), strict: self.strict, io: io.as_ref() }
    }

    /// Interrupt, trap, and exception handler.
    /// 
    /// If priority is none, this will unconditionally initialize the trap or exception handler.
    /// If priority is not none, this will run the interrupt handler only if the interrupt's priority
    /// is greater than the PSR's priority.
    /// 
    /// The address provided is the address into the jump table (either the trap or interrupt vector ones).
    /// This function will always jump to `mem[vect]` at the end of this function.
    pub fn handle_interrupt(&mut self, vect: u16, priority: Option<u8>) -> Result<(), SimErr> {
        if priority.is_some_and(|prio| prio <= self.psr.priority()) { return Ok(()) };
        if vect == 0x25 { return Err(SimErr::ProgramHalted) }; // HALT!
        
        if !self.psr.privileged() {
            std::mem::swap(&mut self.saved_sp, &mut self.reg_file[R6]);
        }

        // Push PSR, PC to supervisor stack
        let old_psr = self.psr.0;
        let old_pc = self.pc;
        
        self.psr.set_privileged(true);
        let mctx = self.mem_ctx(&self.io);
        let sp = &mut self.reg_file[R6];

        *sp -= 1u16;
        self.mem.set(sp.get(), Word::new_init(old_psr), mctx)?;
        *sp -= 1u16;
        self.mem.set(sp.get(), Word::new_init(old_pc), mctx)?;
        
        // set interrupt priority
        if let Some(prio) = priority {
            self.psr.set_priority(prio);
        }

        self.sr_entered += 1;
        let addr = self.mem.get(vect, self.mem_ctx(&self.io))?;
        self.set_pc(addr)
    }

    /// Execute the program.
    pub fn run(&mut self) -> Result<(), SimErr> {
        use std::sync::atomic::Ordering;

        self.mcr.store(true, Ordering::Relaxed);

        // event loop
        while self.mcr.load(Ordering::Relaxed) {
            // if any breakpoints are hit, then stop
            if self.breakpoints.iter().any(|bp| bp.check(self)) {
                break;
            }

            match self.step_in() {
                Ok(_) => {},
                Err(SimErr::ProgramHalted) => break,
                Err(e) => {
                    self.mcr.store(false, Ordering::Release);
                    return Err(e);
                }
            }
        }

        self.mcr.store(false, Ordering::Release);
        Ok(())
    }
    /// Perform one step through the simulator's execution.
    pub fn step_in(&mut self) -> Result<(), SimErr> {
        let word = self.mem.get(self.pc, self.mem_ctx(&self.io))?
            .assert_init(self.strict, SimErr::StrictPCMemUninit)?
            .get();
        let instr = SimInstr::decode(word)?;

        self.offset_pc(1)?;

        match instr {
            SimInstr::BR(cc, off)  => {
                if cc & self.psr.cc() != 0 {
                    self.offset_pc(off.get())?;
                }
            },
            SimInstr::ADD(dr, sr1, sr2) => {
                let val1 = self.reg_file[sr1];
                let val2 = match sr2 {
                    ImmOrReg::Imm(i2) => Word::from(i2.get()),
                    ImmOrReg::Reg(r2) => self.reg_file[r2],
                };

                let result = val1 + val2;
                self.reg_file[dr].copy_word(result, self.strict, SimErr::StrictRegSetUninit)?;
                self.set_cc(result.get());
            },
            SimInstr::LD(dr, off) => {
                let ea = self.pc.wrapping_add_signed(off.get());
                let write_strict = self.strict && !self.in_alloca(ea);

                let val = self.mem.get(ea, self.mem_ctx(&self.io))?;
                self.reg_file[dr].copy_word(val, write_strict, SimErr::StrictRegSetUninit)?;
                self.set_cc(val.get());
            },
            SimInstr::ST(sr, off) => {
                let ea = self.pc.wrapping_add_signed(off.get());
                let write_ctx = MemAccessCtx {
                    strict: self.strict && !self.in_alloca(ea),
                    ..self.mem_ctx(&self.io)
                };

                let val = self.reg_file[sr];
                self.mem.set(ea, val, write_ctx)?;
            },
            SimInstr::JSR(op) => {
                self.reg_file[R7].set(self.pc);

                let addr = match op {
                    ImmOrReg::Imm(off) => Word::from(self.pc.wrapping_add_signed(off.get())),
                    ImmOrReg::Reg(br)  => self.reg_file[br],
                };
                self.sr_entered += 1;
                self.set_pc(addr)?;
            },
            SimInstr::AND(dr, sr1, sr2) => {
                let val1 = self.reg_file[sr1];
                let val2 = match sr2 {
                    ImmOrReg::Imm(i2) => Word::from(i2.get()),
                    ImmOrReg::Reg(r2) => self.reg_file[r2],
                };

                let result = val1 & val2;
                self.reg_file[dr].copy_word(result, self.strict, SimErr::StrictRegSetUninit)?;
                self.set_cc(result.get());
            },
            SimInstr::LDR(dr, br, off) => {
                let ea = self.reg_file[br]
                    .assert_init(self.strict, SimErr::StrictMemAddrUninit)?
                    .get()
                    .wrapping_add_signed(off.get());
                let write_strict = self.strict && br != R6 && !self.in_alloca(ea);
                
                let val = self.mem.get(ea, self.mem_ctx(&self.io))?;
                self.reg_file[dr].copy_word(val, write_strict, SimErr::StrictRegSetUninit)?;
                self.set_cc(val.get());
            },
            SimInstr::STR(sr, br, off) => {
                let ea = self.reg_file[br]
                    .assert_init(self.strict, SimErr::StrictMemAddrUninit)?
                    .get()
                    .wrapping_add_signed(off.get());
                let write_ctx = MemAccessCtx {
                    strict: self.strict && br != R6 && !self.in_alloca(ea),
                    ..self.mem_ctx(&self.io)
                };
                
                let val = self.reg_file[sr];
                self.mem.set(ea, val, write_ctx)?;
            },
            SimInstr::RTI => {
                if self.psr.privileged() {
                    let mctx = self.mem_ctx(&self.io);
                    let sp = (&mut self.reg_file[R6])
                        .assert_init(self.strict, SimErr::StrictMemAddrUninit)?;

                    let pc = self.mem.get(sp.get(), mctx)?
                        .assert_init(self.strict, SimErr::StrictJmpAddrUninit)?
                        .get();
                    *sp += 1u16;
                    let psr = self.mem.get(sp.get(), mctx)?
                        .assert_init(self.strict, SimErr::StrictPSRSetUninit)?
                        .get();
                    *sp += 1u16;

                    self.pc = pc;
                    self.psr = PSR(psr);

                    if !self.psr.privileged() {
                        std::mem::swap(&mut self.saved_sp, &mut self.reg_file[R6]);
                    }

                    self.sr_entered = self.sr_entered.saturating_sub(1);
                } else {
                    return Err(SimErr::PrivilegeViolation);
                }
            },
            SimInstr::NOT(dr, sr) => {
                let val = self.reg_file[sr];
                
                let result = !val;
                self.reg_file[dr].copy_word(result, self.strict, SimErr::StrictRegSetUninit)?;
                self.set_cc(result.get());
            },
            SimInstr::LDI(dr, off) => {
                let shifted_pc = self.pc.wrapping_add_signed(off.get());
                let ea = self.mem.get(shifted_pc, self.mem_ctx(&self.io))?
                    .assert_init(self.strict, SimErr::StrictMemAddrUninit)?
                    .get();
                let write_strict = self.strict && !self.in_alloca(ea);

                let val = self.mem.get(ea, self.mem_ctx(&self.io))?;
                self.reg_file[dr].copy_word(val, write_strict, SimErr::StrictRegSetUninit)?;
                self.set_cc(val.get());
            },
            SimInstr::STI(sr, off) => {
                let shifted_pc = self.pc.wrapping_add_signed(off.get());
                let ea = self.mem.get(shifted_pc, self.mem_ctx(&self.io))?
                    .assert_init(self.strict, SimErr::StrictMemAddrUninit)?
                    .get();
                let write_ctx = MemAccessCtx {
                    strict: self.strict && !self.in_alloca(ea),
                    ..self.mem_ctx(&self.io)
                };

                let val = self.reg_file[sr];
                self.mem.set(ea, val, write_ctx)?;
            },
            SimInstr::JMP(br) => {
                // check for RET
                if br.0 == 7 {
                    self.sr_entered = self.sr_entered.saturating_sub(1);
                }
                let addr = self.reg_file[br];
                self.set_pc(addr)?;
            },
            SimInstr::LEA(dr, off) => {
                let ea = self.pc.wrapping_add_signed(off.get());
                self.reg_file[dr].set(ea);
            },
            SimInstr::TRAP(vect) => {
                self.handle_interrupt(vect.get(), None)?;
            },
        }

        Ok(())
    }
    /// Perform one step through the simulator's execution, treating complete subroutines as one step.
    pub fn step_over(&mut self) -> Result<(), SimErr> {
        let curr_frame = self.sr_entered;
        self.step_in()?;
        // step until we have landed back in the same frame
        while curr_frame < self.sr_entered {
            self.step_in()?;
        }

        Ok(())
    }
    /// Run through the simulator's execution until the subroutine is exited.
    pub fn step_out(&mut self) -> Result<(), SimErr> {
        let curr_frame = self.sr_entered;
        self.step_in()?;
        // step until we get out of this frame
        while curr_frame != 0 && curr_frame <= self.sr_entered {
            self.step_in()?;
        }

        Ok(())
    }
}
impl Default for Simulator {
    fn default() -> Self {
        Self::new()
    }
}

/// A wrapper over `u16` in order to faciliate the PSR.
/// 
/// The word is encoded as the following:
/// - `PSR[15..16]`: Privilege mode (0 = supervisor, 1 = user)
/// - `PSR[8..11]`:  Interrupt priority
/// - `PSR[0..3]`:   Condition codes
/// 
/// Each of these are exposed as the [`PSR::privileged`], [`PSR::priority`], and [`PSR::cc`] values.
#[allow(clippy::upper_case_acronyms)]
#[repr(transparent)]
pub struct PSR(pub u16);

impl PSR {
    /// Creates a PSR with a default value.
    pub fn new() -> Self {
        PSR(0x8002)
    }

    /// Checks whether the simulator is in privileged mode.
    /// - `true` = supervisor mode
    /// - `false` = user mode
    pub fn privileged(&self) -> bool {
        (self.0 >> 15) == 0
    }
    /// Checks the current interrupt priority of the simulator.
    pub fn priority(&self) -> u8 {
        ((self.0 >> 8) & 0b111) as u8
    }
    /// Checks the condition code of the simulator.
    pub fn cc(&self) -> u8 {
        (self.0 & 0b111) as u8
    }
    /// Sets whether the simulator is in privileged mode.
    pub fn set_privileged(&mut self, privl: bool) {
        self.0 &= 0x7FFF;
        self.0 |= (!privl as u16) << 15;
    }
    /// Sets the current interrupt priority of the simulator.
    pub fn set_priority(&mut self, prio: u8) {
        self.0 &= 0xF8FF;
        self.0 |= (prio as u16) << 8;
    }
    /// Sets the condition code of the simulator.
    pub fn set_cc(&mut self, cc: u8) {
        self.0 &= 0xFFF8;
        self.0 |= cc as u16;
    }
}
impl Default for PSR {
    fn default() -> Self {
        Self::new()
    }
}
impl std::fmt::Debug for PSR {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        use std::fmt::Write;
        struct CC(u8);

        impl std::fmt::Debug for CC {
            fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                if self.0 & 0b100 != 0 { f.write_char('N')?; };
                if self.0 & 0b010 != 0 { f.write_char('Z')?; };
                if self.0 & 0b001 != 0 { f.write_char('P')?; };
                Ok(())
            }
        }

        f.debug_struct("PSR")
            .field("privileged", &self.privileged())
            .field("priority", &self.priority())
            .field("cc", &CC(self.cc()))
            .finish()
    }
}