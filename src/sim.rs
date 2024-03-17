//! Simulating and execution for LC-3 assembly.
//! 
//! This module is focused on executing fully assembled code (i.e., [`ObjectFile`]).
//! 
//! This module consists of:
//! - [`Simulator`]: The struct that simulates assembled code.
//! - [`Word`]: A mutable memory location.
use std::ops::Range;

use crate::asm::ObjectFile;
use crate::ast::sim::SimInstr;
use crate::ast::Reg;

/// Errors that can occur during simulation.
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
    ProgramHalted
}

const USER_RANGE: Range<u16> = 0x3000..0xFE00;

/// Executes assembled code.
#[derive(Debug)]
pub struct Simulator {
    mem: [Word; 2usize.pow(16)],
    reg_file: [Word; 8],
    /// The program counter.
    pc: u16,
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
    sr_entered: u64
}

impl Simulator {
    /// Creates a new simulator, without any object files loaded.
    pub fn new() -> Self {
        Self {
            mem: std::array::from_fn(|_| Word::new_uninit()),
            reg_file: std::array::from_fn(|_| Word::new_uninit()),
            pc: 0x3000,
            psr: 0x8002,
            saved_sp: Word::new_init(0x2FFF),
            sr_entered: 0
        }
    }
    /// Loads an object file into this simulator.
    pub fn load_obj_file(&mut self, obj: &ObjectFile) {
        for (&start, words) in obj.iter() {
            let end = start.wrapping_add(words.len() as u16);
            if start <= end {
                // contiguous copy
                let range = (start as usize)..(end as usize);
                self.mem[range].copy_from_slice(words);
            } else {
                // discontiguous copy
                let len = start.wrapping_neg() as usize;
                let (left, right) = words.split_at(len);
                self.mem[(start as usize)..].copy_from_slice(left);
                self.mem[..(end as usize)].copy_from_slice(right);
            }
        }
    }
    /// Wipes the simulator's state.
    pub fn clear(&mut self) {
        std::mem::take(self);
    }

    /// Accesses a word in memory (allowing both reads and writes).
    /// 
    /// See [`Word`] for more details.
    pub fn access_mem(&mut self, addr: u16) -> &mut Word {
        &mut self.mem[addr as usize]
    }
    /// Accesses a word from a register (allowing both reads and writes).
    /// 
    /// See [`Word`] for more details.
    pub fn access_reg(&mut self, reg: Reg) -> &mut Word {
        &mut self.reg_file[reg.0 as usize]
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
    pub fn set_pc(&mut self, addr: u16) -> Result<(), SimErr> {
        // Check access violation
        if !self.is_privileged() && !USER_RANGE.contains(&addr) {
            return Err(SimErr::AccessViolation);
        }

        self.pc = addr;
        Ok(())
    }
    /// Adds an offset to the PC.
    pub fn offset_pc(&mut self, offset: i16) -> Result<(), SimErr> {
        self.set_pc(self.pc.wrapping_add_signed(offset))
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
            std::mem::swap(&mut self.saved_sp, &mut self.reg_file[6]);
        }

        // Push PSR, PC to supervisor stack
        let mut sp = self.reg_file[6];
        let old_psr = self.psr;
        let old_pc = self.pc;
        
        sp -= 1u16;
        self.access_mem(sp.get_unsigned()).set(old_psr);
        sp -= 1u16;
        self.access_mem(sp.get_unsigned()).set(old_pc);
        
        self.psr &= 0x7FFF; // set privileged

        // set interrupt priority
        if let Some(prio) = priority {
            self.psr &= !(0b111 << 8);
            self.psr |= (prio as u16 & 0b111) << 8;
        }

        self.sr_entered += 1;
        let addr = self.access_mem(vect).get_unsigned();
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
        let word = self.access_mem(self.pc).get_unsigned();
        let instr = SimInstr::decode(word)?;
        self.offset_pc(1)?;

        match instr {
            SimInstr::BR(cc, off)  => {
                if (cc as u16) & self.psr & 0b111 != 0 {
                    self.offset_pc(off.get())?;
                }
            },
            SimInstr::ADD(dr, sr1, sr2) => {
                let val1 = *self.access_reg(sr1);
                let val2 = match sr2 {
                    crate::ast::ImmOrReg::Imm(i2) => Word::new_init(i2.get() as u16),
                    crate::ast::ImmOrReg::Reg(r2) => *self.access_reg(r2),
                };

                let result = val1 + val2;
                self.access_reg(dr).copy_word(result);
                self.set_cc(result.get_signed());
            },
            SimInstr::LD(dr, off) => {
                let ea = self.pc.wrapping_add_signed(off.get());
                
                let val = *self.access_mem(ea);
                self.access_reg(dr).copy_word(val);
                self.set_cc(val.get_signed());
            },
            SimInstr::ST(sr, off) => {
                let ea = self.pc.wrapping_add_signed(off.get());

                let val = *self.access_reg(sr);
                self.access_mem(ea).copy_word(val);
            },
            SimInstr::JSR(op) => {
                let off = match op {
                    crate::ast::ImmOrReg::Imm(off) => off.get(),
                    crate::ast::ImmOrReg::Reg(br)  => self.access_reg(br).get_signed(),
                };

                self.reg_file[7].set(self.pc);
                self.sr_entered += 1;
                self.offset_pc(off)?;
            },
            SimInstr::AND(dr, sr1, sr2) => {
                let val1 = *self.access_reg(sr1);
                let val2 = match sr2 {
                    crate::ast::ImmOrReg::Imm(i2) => Word::new_init(i2.get() as u16),
                    crate::ast::ImmOrReg::Reg(r2) => *self.access_reg(r2),
                };

                let result = val1 & val2;
                self.access_reg(dr).copy_word(result);
                self.set_cc(result.get_signed());
            },
            SimInstr::LDR(dr, br, off) => {
                let ea = self.access_reg(br).get_unsigned().wrapping_add_signed(off.get());

                let val = *self.access_mem(ea);
                self.access_reg(dr).copy_word(val);
                self.set_cc(val.get_signed());
            },
            SimInstr::STR(sr, br, off) => {
                let ea = self.access_reg(br).get_unsigned().wrapping_add_signed(off.get());
                
                let val = *self.access_reg(sr);
                self.access_mem(ea).copy_word(val);
            },
            SimInstr::RTI => {
                if self.is_privileged() {
                    let mut sp = self.reg_file[6];

                    let pc = self.access_mem(sp.get_unsigned()).get_unsigned();
                    sp += 1u16;
                    let psr = self.access_mem(sp.get_unsigned()).get_unsigned();
                    sp += 1u16;

                    self.pc = pc;
                    self.psr = psr;

                    if !self.is_privileged() {
                        std::mem::swap(&mut self.saved_sp, &mut self.reg_file[6]);
                    }

                    self.sr_entered = self.sr_entered.saturating_sub(1);
                } else {
                    return Err(SimErr::PrivilegeViolation);
                }
            },
            SimInstr::NOT(dr, sr) => {
                let val = *self.access_reg(sr);
                
                let result = !val;
                self.access_reg(dr).copy_word(result);
                self.set_cc(result.get_signed());
            },
            SimInstr::LDI(dr, off) => {
                let ea = self.access_mem(self.pc.wrapping_add_signed(off.get())).get_unsigned();

                let val = *self.access_mem(ea);
                self.access_reg(dr).copy_word(val);
                self.set_cc(val.get_signed());
            },
            SimInstr::STI(sr, off) => {
                let ea = self.access_mem(self.pc.wrapping_add_signed(off.get())).get_unsigned();

                let val = *self.access_reg(sr);
                self.access_mem(ea).copy_word(val);
            },
            SimInstr::JMP(br) => {
                let off = self.access_reg(br).get_unsigned();
                // check for RET
                if br.0 == 7 {
                    self.sr_entered = self.sr_entered.saturating_sub(1);
                }

                self.set_pc(off)?;
            },
            SimInstr::LEA(dr, off) => {
                let ea = self.pc.wrapping_add_signed(off.get());
                self.access_reg(dr).set(ea);
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

/// A memory location that can be read and written to.
/// 
/// # Reading
/// 
/// A word can be read as either an unsigned integer or a signed one.
/// - [`Word::get_unsigned`] to read the word as unsigned
/// - [`Word::get_signed`] to read the word as signed
/// 
/// # Writing
/// 
/// A word can be written into with a value or with another word.
/// - [`Word::set`] to read a value into this word
/// - [`Word::copy_word`] to read a word into this word
/// 
/// `copy_word` may be more useful in situations where initialization state may want to be preserved.
/// See [`Word::set`] for more details.
/// 
/// Words can also be written to by applying assign operations (e.g., add, sub, and, etc.).
/// All arithmetic operations that can be applied to words are assumed to be wrapping.
/// See those implementations for more details.
#[derive(Debug, Clone, Copy)]
pub struct Word {
    data: u16,
    init: u16
}

const NO_BITS:  u16 = 0;
const ALL_BITS: u16 = 1u16.wrapping_neg();
impl Word {
    /// Creates a new word that is considered uninitialized.
    pub fn new_uninit() -> Self {
        Self {
            data: 0,
            init: NO_BITS,
        }
    }
    /// Creates a new word that is initialized with a given data value.
    pub fn new_init(data: u16) -> Self {
        Self {
            data,
            init: ALL_BITS,
        }
    }

    /// Reads the word, returning its unsigned representation.
    pub fn get_unsigned(&self) -> u16 {
        self.data
    }
    /// Reads the word, returning its signed representation.
    pub fn get_signed(&self) -> i16 {
        self.data as i16
    }

    /// Checks that a word is fully initialized
    pub fn is_init(&self) -> bool {
        self.init == ALL_BITS
    }

    /// Writes to the word.
    /// 
    /// The data provided is assumed to be FULLY initialized,
    /// and will set the initialization state of this word to be
    /// fully initialized.
    /// 
    /// If the data is not fully initialized (e.g., if it is a partially initialized word),
    /// [`Word::copy_word`] can be used instead.
    pub fn set(&mut self, data: u16) {
        self.data = data;
        self.init = ALL_BITS;
    }
    /// Copies the data from one word into another.
    /// 
    /// This is useful for preserving initialization state.
    pub fn copy_word(&mut self, word: Word) {
        *self = word;
    }
}

/** NOT **/
impl std::ops::Not for Word {
    type Output = Word;

    /// Inverts the data on this word, preserving any initialization state.
    fn not(self) -> Self::Output {
        // Initialization state should stay the same after this.
        let Self { data, init } = self;
        Self { data: !data, init }
    }
}

/** ADD **/
impl std::ops::Add for Word {
    type Output = Word;

    /// Adds two words together (wrapping if overflow occurs).
    /// 
    /// If the two words are fully initialized, 
    /// the resulting word will also be fully initialized.
    /// Otherwise, the resulting word is fully uninitialized.
    fn add(self, rhs: Self) -> Self::Output {
        let Self { data: ldata, init: linit } = self;
        let Self { data: rdata, init: rinit } = rhs;

        let data = ldata.wrapping_add(rdata);
        // Very lazy initialization scheme.
        // If both are fully init, consider this word fully init.
        // Otherwise, consider it fully uninit.
        let init = match linit == ALL_BITS && rinit == ALL_BITS {
            true  => ALL_BITS,
            false => NO_BITS,
        };

        Self { data, init }
    }
}
impl std::ops::AddAssign for Word {
    fn add_assign(&mut self, rhs: Self) {
        *self = *self + rhs;
    }
}
impl std::ops::AddAssign<u16> for Word {
    /// Increments the word by the provided value.
    /// 
    /// If the word was fully initialized,
    /// its updated value is also fully initialized.
    /// Otherwise, the resulting word is fully uninitialized.
    fn add_assign(&mut self, rhs: u16) {
        *self = *self + Word::new_init(rhs);
    }
}
impl std::ops::AddAssign<i16> for Word {
    /// Increments the word by the provided value.
    /// 
    /// If the word was fully initialized,
    /// its updated value is also fully initialized.
    /// Otherwise, the resulting word is fully uninitialized.
    fn add_assign(&mut self, rhs: i16) {
        *self = *self + Word::new_init(rhs as _);
    }
}

/** SUB **/
impl std::ops::Sub for Word {
    type Output = Word;

    /// Subtracts two words together (wrapping if overflow occurs).
    /// 
    /// If the two words are fully initialized, 
    /// the resulting word will also be fully initialized.
    /// Otherwise, the resulting word is fully uninitialized.
    fn sub(self, rhs: Self) -> Self::Output {
        let Self { data: ldata, init: linit } = self;
        let Self { data: rdata, init: rinit } = rhs;

        let data = ldata.wrapping_sub(rdata);
        // Very lazy initialization scheme.
        // If both are fully init, consider this word fully init.
        // Otherwise, consider it fully uninit.
        let init = match linit == ALL_BITS && rinit == ALL_BITS {
            true  => ALL_BITS,
            false => NO_BITS,
        };

        Self { data, init }
    }
}
impl std::ops::SubAssign for Word {
    fn sub_assign(&mut self, rhs: Self) {
        *self = *self - rhs;
    }
}
impl std::ops::SubAssign<u16> for Word {
    /// Decrements the word by the provided value.
    /// 
    /// If the word was fully initialized,
    /// its updated value is also fully initialized.
    /// Otherwise, the resulting word is fully uninitialized.
    fn sub_assign(&mut self, rhs: u16) {
        *self = *self - Word::new_init(rhs);
    }
}
impl std::ops::SubAssign<i16> for Word {
    /// Decrements the word by the provided value.
    /// 
    /// If the word was fully initialized,
    /// its updated value is also fully initialized.
    /// Otherwise, the resulting word is fully uninitialized.
    fn sub_assign(&mut self, rhs: i16) {
        *self = *self - Word::new_init(rhs as _);
    }
}

/** AND **/
impl std::ops::BitAnd for Word {
    type Output = Word;

    /// Applies a bitwise AND across two words.
    /// 
    /// This will also compute the correct initialization
    /// for the resulting word, taking into account bit clearing.
    fn bitand(self, rhs: Self) -> Self::Output {
        let Self { data: ldata, init: linit } = self;
        let Self { data: rdata, init: rinit } = rhs;

        let data = ldata & rdata;
        // A given bit of the result is init if:
        // - both the lhs and rhs bits are init
        // - either of the bits are data: 0, init: 1
        let init = (linit & rinit) | (!ldata & linit) | (!rdata & rinit);

        Self { data, init }
    }
}
impl std::ops::BitAndAssign for Word {
    fn bitand_assign(&mut self, rhs: Self) {
        *self = *self & rhs;
    }
}