//! Simulating and execution for LC-3 assembly.
//! 
//! This module is focused on executing fully assembled code (i.e., [`ObjectFile`]).
//! 
//! This module consists of:
//! - [`Simulator`]: The struct that simulates assembled code.
//! - [`Word`]: A mutable memory location.
//! - [`WordArray`]: An array of memory locations, which can be indexed with non-usize types

mod word;

use std::ops::Range;

use crate::asm::ObjectFile;
use crate::ast::reg_consts::{R6, R7};
use crate::ast::sim::SimInstr;
use crate::ast::{ImmOrReg, Reg};
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

const USER_RANGE: Range<u16> = 0x3000..0xFE00;

/// Macro that asserts that a given word is fully initialized in strict mode.
/// 
/// While in strict mode, 
/// - if the word is fully initialized, this returns the initialized word ref/mut ref/value.
/// - if the word is not fully initialized, this errors with the provided error.
/// 
/// While not in strict mode, this does nothing.
macro_rules! assert_init {
    ($word:expr, $strict:expr, $err:expr) => {
        {
            let w = $word;
            match $strict && !w.is_init() {
                true => Err($err),
                false => Ok(w)
            }
        }
    }
}
/// Executes assembled code.
#[derive(Debug)]
pub struct Simulator {
    /// The simulator's memory.
    /// 
    /// Note that this is held in the heap, as it is too large for the stack.
    pub mem: WordArray<Box<[Word; 2usize.pow(16)]>, u16>,

    /// The simulator's register file.
    pub reg_file: WordArray<[Word; 8], Reg>,

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
            mem: WordArray::new(),
            reg_file: WordArray::new(),
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
            let end = start.wrapping_add(words.len() as u16);
            let mem = &mut *self.mem;
            if start <= end {
                // contiguous copy
                let range = (start as usize)..(end as usize);
                mem[range].copy_from_slice(words);
            } else {
                // discontiguous copy
                let len = start.wrapping_neg() as usize;
                let (left, right) = words.split_at(len);
                mem[(start as usize)..].copy_from_slice(left);
                mem[..(end as usize)].copy_from_slice(right);
            }
        }
    }
    /// Wipes the simulator's state.
    pub fn clear(&mut self) {
        std::mem::take(self);
    }

    /// Sets the condition codes using the provided result.
    fn set_cc(&mut self, result: i16) {
        self.psr &= 0xFFF8;
        match result.cmp(&0) {
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
    pub fn set_pc(&mut self, word: Word) -> Result<(), SimErr> {
        let addr = word.get_unsigned();
        if self.strict {
            // Check PC is initialized:
            if !word.is_init() { return Err(SimErr::StrictJmpAddrUninit) };
            if !self.mem[addr].is_init() { return Err(SimErr::StrictPCMemUninit) };
        }

        // Check access violation
        if !self.is_privileged() && !USER_RANGE.contains(&addr) {
            return Err(SimErr::AccessViolation);
        }

        self.pc = addr;
        Ok(())
    }
    /// Adds an offset to the PC.
    pub fn offset_pc(&mut self, offset: i16) -> Result<(), SimErr> {
        self.set_pc(Word::from(self.pc.wrapping_add_signed(offset)))
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
        let mut sp = self.reg_file[R6];
        let old_psr = self.psr;
        let old_pc = self.pc;
        
        sp -= 1u16;
        self.mem[sp.get_unsigned()].set(old_psr);
        sp -= 1u16;
        self.mem[sp.get_unsigned()].set(old_pc);
        
        self.psr &= 0x7FFF; // set privileged

        // set interrupt priority
        if let Some(prio) = priority {
            self.psr &= !(0b111 << 8);
            self.psr |= (prio as u16 & 0b111) << 8;
        }

        self.sr_entered += 1;
        let addr = self.mem[vect];
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
        let word = self.mem[self.pc].get_unsigned();
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

                let result = assert_init!(val1 + val2, self.strict, SimErr::StrictRegSetUninit)?;
                self.reg_file[dr].copy_word(result);
                self.set_cc(result.get_signed());
            },
            SimInstr::LD(dr, off) => {
                let ea = self.pc.wrapping_add_signed(off.get());
                
                let val = assert_init!(self.mem[ea], self.strict, SimErr::StrictRegSetUninit)?;
                self.reg_file[dr].copy_word(val);
                self.set_cc(val.get_signed());
            },
            SimInstr::ST(sr, off) => {
                let ea = self.pc.wrapping_add_signed(off.get());

                let val = assert_init!(self.reg_file[sr], self.strict, SimErr::StrictRegSetUninit)?;
                self.mem[ea].copy_word(val);
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

                let result = assert_init!(val1 & val2, self.strict, SimErr::StrictRegSetUninit)?;
                self.reg_file[dr].copy_word(result);
                self.set_cc(result.get_signed());
            },
            SimInstr::LDR(dr, br, off) => {
                let ea = assert_init!(self.reg_file[br], self.strict, SimErr::StrictMemAddrUninit)?
                    .get_unsigned()
                    .wrapping_add_signed(off.get());

                let val = assert_init!(self.mem[ea], self.strict, SimErr::StrictRegSetUninit)?;
                self.reg_file[dr].copy_word(val);
                self.set_cc(val.get_signed());
            },
            SimInstr::STR(sr, br, off) => {
                let ea = assert_init!(self.reg_file[br], self.strict, SimErr::StrictMemAddrUninit)?
                    .get_unsigned()
                    .wrapping_add_signed(off.get());
                
                let val = assert_init!(self.reg_file[sr], self.strict, SimErr::StrictMemSetUninit)?;
                self.mem[ea].copy_word(val);
            },
            SimInstr::RTI => {
                if self.is_privileged() {
                    let mut sp = assert_init!(self.reg_file[R6], self.strict, SimErr::StrictMemAddrUninit)?;

                    let pc  = assert_init!(self.mem[sp.get_unsigned()], self.strict, SimErr::StrictJmpAddrUninit)?
                        .get_unsigned();
                    sp += 1u16;
                    let psr = assert_init!(self.mem[sp.get_unsigned()], self.strict, SimErr::StrictPSRSetUninit)?
                        .get_unsigned();
                    sp += 1u16;

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
                
                let result = assert_init!(!val, self.strict, SimErr::StrictRegSetUninit)?;
                self.reg_file[dr].copy_word(result);
                self.set_cc(result.get_signed());
            },
            SimInstr::LDI(dr, off) => {
                let shifted_pc = self.pc.wrapping_add_signed(off.get());
                let ea = assert_init!(self.mem[shifted_pc], self.strict, SimErr::StrictMemAddrUninit)?
                    .get_unsigned();

                let val = assert_init!(self.mem[ea], self.strict, SimErr::StrictRegSetUninit)?;
                self.reg_file[dr].copy_word(val);
                self.set_cc(val.get_signed());
            },
            SimInstr::STI(sr, off) => {
                let shifted_pc = self.pc.wrapping_add_signed(off.get());
                let ea = assert_init!(self.mem[shifted_pc], self.strict, SimErr::StrictMemAddrUninit)?
                    .get_unsigned();

                let val = assert_init!(self.reg_file[sr], self.strict, SimErr::StrictMemSetUninit)?;
                self.mem[ea].copy_word(val);
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