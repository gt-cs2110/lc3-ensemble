//! Simulating and execution for LC-3 assembly.
//! 
//! This module is focused on executing fully assembled code (i.e., [`ObjectFile`]).
//! 
//! This module consists of:
//! - [`Simulator`]: The struct that simulates assembled code.
//! - [`Word`]: A mutable memory location.
//! - [`WordArray`]: An array of memory locations, which can be indexed with non-usize types

mod word;

use crate::asm::ObjectFile;
use crate::ast::reg_consts::{R6, R7};
use crate::ast::sim::SimInstr;
use crate::ast::ImmOrReg;
pub use word::*;

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
    StrictRegSetUninit,
    /// Data was stored into memory with a partially uninitialized value.
    StrictMemSetUninit,
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

    /// The processor status register.
    /// 
    /// - `PSR[15..16]`: Privilege mode (0 = supervisor, 1 = user)
    /// - `PSR[8..11]`:  Interrupt priority
    /// - `PSR[0..3]`:   Condition codes
    psr: u16,

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
    strict: bool
}

impl Simulator {
    /// Creates a new simulator, without any object files loaded.
    pub fn new() -> Self {
        Self {
            mem: Mem::new(),
            reg_file: RegFile::new(),
            pc: 0x3000,
            psr: 0x8002,
            saved_sp: Word::new_init(0x2FFF),
            sr_entered: 0,
            strict: false
        }
    }

    /// Loads an object file into this simulator.
    pub fn load_obj_file(&mut self, obj: &ObjectFile) {
        for (&start, words) in obj.iter() {
            self.mem.copy_block(start, words);
        }
    }
    /// Wipes the simulator's state.
    pub fn clear(&mut self) {
        std::mem::take(self);
    }

    /// Sets the condition codes using the provided result.
    fn set_cc(&mut self, result: u16) {
        self.psr &= 0xFFF8;
        match (result as i16).cmp(&0) {
            std::cmp::Ordering::Less    => self.psr |= 0b100,
            std::cmp::Ordering::Equal   => self.psr |= 0b010,
            std::cmp::Ordering::Greater => self.psr |= 0b001,
        }
    }
    /// Checks if the simulator is in privileged mode.
    pub fn is_privileged(&self) -> bool {
        (self.psr & 0x8000) == 0
    }

    /// Checks the PSR's priority.
    pub fn priority(&self) -> u8 {
        ((self.psr >> 8) & 0b111) as u8
    }
    
    /// Sets the PC to the given address, raising any errors that occur.
    pub fn set_pc(&mut self, addr_word: Word) -> Result<(), SimErr> {
        let addr = addr_word.get();
        let data = self.mem.get(addr, self.mem_ctx())?;

        if self.strict {
            // Check PC address is initialized:
            if !addr_word.is_init() { return Err(SimErr::StrictJmpAddrUninit) };
            // Check data at PC is initialized:
            if !data.is_init() { return Err(SimErr::StrictPCMemUninit) };
        }

        self.pc = addr;
        Ok(())
    }
    /// Adds an offset to the PC.
    pub fn offset_pc(&mut self, offset: i16) -> Result<(), SimErr> {
        self.set_pc(Word::from(self.pc.wrapping_add_signed(offset)))
    }

    /// Computes the memory access context, 
    /// which are flags that control privilege and checks when accessing memory.
    pub fn mem_ctx(&self) -> MemAccessCtx {
        MemAccessCtx { privileged: self.is_privileged(), strict: self.strict }
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
        if priority.is_some_and(|prio| prio <= self.priority()) { return Ok(()) };
        if vect == 0x25 { return Err(SimErr::ProgramHalted) }; // HALT!
        
        if !self.is_privileged() {
            std::mem::swap(&mut self.saved_sp, &mut self.reg_file[R6]);
        }

        // Push PSR, PC to supervisor stack
        let old_psr = self.psr;
        let old_pc = self.pc;
        
        self.psr &= 0x7FFF; // set privileged
        let mctx = self.mem_ctx();
        let sp = &mut self.reg_file[R6];

        *sp -= 1u16;
        self.mem.set(sp.get(), Word::new_init(old_psr), mctx)?;
        *sp -= 1u16;
        self.mem.set(sp.get(), Word::new_init(old_pc), mctx)?;
        
        // set interrupt priority
        if let Some(prio) = priority {
            self.psr &= !(0b111 << 8);
            self.psr |= (prio as u16 & 0b111) << 8;
        }

        self.sr_entered += 1;
        let addr = self.mem.get(vect, self.mem_ctx())?;
        self.set_pc(addr)
    }
    /// Start the simulator's execution.
    pub fn start(&mut self) -> Result<(), SimErr> {
        loop {
            self.step_in()?;
        }
    }
    /// Perform one step through the simulator's execution.
    pub fn step_in(&mut self) -> Result<(), SimErr> {
        let word = self.mem.get(self.pc, self.mem_ctx())?.get();
        let instr = SimInstr::decode(word)?;
        self.offset_pc(1)?;

        match instr {
            SimInstr::BR(cc, off)  => {
                if (cc as u16) & self.psr & 0b111 != 0 {
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
                
                let val = self.mem.get(ea, self.mem_ctx())?;
                self.reg_file[dr].copy_word(val, self.strict, SimErr::StrictRegSetUninit)?;
                self.set_cc(val.get());
            },
            SimInstr::ST(sr, off) => {
                let ea = self.pc.wrapping_add_signed(off.get());

                let val = self.reg_file[sr];
                self.mem.set(ea, val, self.mem_ctx())?;
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

                let val = self.mem.get(ea, self.mem_ctx())?;
                self.reg_file[dr].copy_word(val, self.strict, SimErr::StrictRegSetUninit)?;
                self.set_cc(val.get());
            },
            SimInstr::STR(sr, br, off) => {
                let ea = self.reg_file[br]
                    .assert_init(self.strict, SimErr::StrictMemAddrUninit)?
                    .get()
                    .wrapping_add_signed(off.get());
                
                let val = self.reg_file[sr];
                self.mem.set(ea, val, self.mem_ctx())?;
            },
            SimInstr::RTI => {
                if self.is_privileged() {
                    let mctx = self.mem_ctx();
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
                    self.psr = psr;

                    if !self.is_privileged() {
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
                let ea = self.mem.get(shifted_pc, self.mem_ctx())?
                    .assert_init(self.strict, SimErr::StrictMemAddrUninit)?
                    .get();

                let val = self.mem.get(ea, self.mem_ctx())?;
                self.reg_file[dr].copy_word(val, self.strict, SimErr::StrictRegSetUninit)?;
                self.set_cc(val.get());
            },
            SimInstr::STI(sr, off) => {
                let shifted_pc = self.pc.wrapping_add_signed(off.get());
                let ea = self.mem.get(shifted_pc, self.mem_ctx())?
                    .assert_init(self.strict, SimErr::StrictMemAddrUninit)?
                    .get();

                let val = self.reg_file[sr];
                self.mem.set(ea, val, self.mem_ctx())?;
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