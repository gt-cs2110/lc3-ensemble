//! Simulating and execution for LC-3 assembly.
//! 
//! This module is focused on executing fully assembled code (i.e., [`ObjectFile`]).
//! 
//! This module consists of:
//! - [`Simulator`]: The struct that simulates assembled code.
//! - [`Word`]: A mutable memory location.
use crate::asm::ObjectFile;
use crate::ast::sim::SimInstr;
use crate::ast::Reg;

/// Errors that can occur during simulation.
pub enum SimErr {
    /// Word was decoded, but the opcode was invalid.
    InvalidOpcode,
    /// Word was decoded, and the opcode is recognized,
    /// but the instruction's format is invalid.
    InvalidInstrFormat
}

/// Executes assembled code.
#[derive(Debug)]
pub struct Simulator {
    mem: [Word; 2usize.pow(16)],
    reg_file: [Word; 8],
    /// The program counter.
    pc: u16,
    /// Condition codes
    // FIXME: upgrade this to the PSR
    cc: u8,

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
            cc: 0b010,
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
    fn set_cc(&mut self, result: u16) {
        match (result as i16).cmp(&0) {
            std::cmp::Ordering::Less    => self.cc = 0b100,
            std::cmp::Ordering::Equal   => self.cc = 0b010,
            std::cmp::Ordering::Greater => self.cc = 0b001,
        }
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
        self.pc += 1;

        match instr {
            SimInstr::BR(cc, off)  => {
                if cc & self.cc != 0 {
                    self.pc = self.pc.wrapping_add_signed(off.get());
                }
            },
            SimInstr::ADD(dr, sr1, sr2) => {
                let val1 = self.access_reg(sr1).get_unsigned();
                let val2 = match sr2 {
                    crate::ast::ImmOrReg::Imm(i2) => i2.get(),
                    crate::ast::ImmOrReg::Reg(r2) => self.access_reg(r2).get_signed(),
                };

                let result = val1.wrapping_add_signed(val2);
                self.access_reg(dr).set(result);
                self.set_cc(result);
            },
            SimInstr::LD(dr, off) => {
                let ea = self.pc.wrapping_add_signed(off.get());
                
                let val = *self.access_mem(ea);
                self.access_reg(dr).copy_word(val);
                self.set_cc(val.get_unsigned());
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

                self.reg_file[0b111].set(self.pc);
                self.pc = self.pc.wrapping_add_signed(off);
                self.sr_entered += 1;
            },
            SimInstr::AND(dr, sr1, sr2) => {
                let val1 = self.access_reg(sr1).get_unsigned();
                let val2 = match sr2 {
                    crate::ast::ImmOrReg::Imm(i2) => i2.get() as u16,
                    crate::ast::ImmOrReg::Reg(r2) => self.access_reg(r2).get_unsigned(),
                };

                let result = val1 & val2;
                self.access_reg(dr).set(result);
                self.set_cc(result);
            },
            SimInstr::LDR(dr, br, off) => {
                let ea = self.access_reg(br).get_unsigned().wrapping_add_signed(off.get());

                let val = *self.access_mem(ea);
                self.access_reg(dr).copy_word(val);
                self.set_cc(val.get_unsigned());
            },
            SimInstr::STR(sr, br, off) => {
                let ea = self.access_reg(br).get_unsigned().wrapping_add_signed(off.get());
                
                let val = *self.access_reg(sr);
                self.access_mem(ea).copy_word(val);
            },
            SimInstr::RTI => todo!("rti not yet implemented"),
            SimInstr::NOT(dr, sr) => {
                let val1 = self.access_reg(sr).get_unsigned();
                
                let result = !val1;
                self.access_reg(dr).set(result);
                self.set_cc(result);
            },
            SimInstr::LDI(dr, off) => {
                let ea = self.access_mem(self.pc.wrapping_add_signed(off.get())).get_unsigned();

                let val = *self.access_mem(ea);
                self.access_reg(dr).copy_word(val);
                self.set_cc(val.get_unsigned());
            },
            SimInstr::STI(sr, off) => {
                let ea = self.access_mem(self.pc.wrapping_add_signed(off.get())).get_unsigned();

                let val = *self.access_reg(sr);
                self.access_mem(ea).copy_word(val);
            },
            SimInstr::JMP(br) => {
                let off = self.access_reg(br).get_signed();
                self.pc = self.pc.wrapping_add_signed(off);

                // check for RET
                if br.0 == 7 {
                    self.sr_entered = self.sr_entered.saturating_sub(1);
                }
            },
            SimInstr::LEA(dr, off) => {
                let ea = self.pc.wrapping_add_signed(off.get());
                self.access_reg(dr).set(ea);
            },
            SimInstr::TRAP(vect) => {
                self.pc = self.access_mem(vect.get()).get_unsigned();
                self.sr_entered += 1;
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
#[derive(Debug, Clone, Copy)]
pub struct Word {
    data: u16,
    init: bool 
}
impl Word {
    /// Creates a new word that is considered uninitialized.
    pub fn new_uninit() -> Self {
        Self {
            data: 0,
            init: false,
        }
    }
    /// Creates a new word that is initialized with a given data value.
    pub fn new_init(data: u16) -> Self {
        Self {
            data,
            init: true,
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
    /// Writes to the word.
    pub fn set(&mut self, data: u16) {
        self.data = data;
        self.init = true;
    }
    /// Copies the data from one word into another.
    /// 
    /// This is useful for preserving initialization state.
    pub fn copy_word(&mut self, word: Word) {
        *self = word;
    }
}