//! This module is used for holding simulation instructions ([`SimInstr`]),
//! which are instructions that directly map to bytecode.
//! 
//! For instructions that map to assembly code, see [`asm::AsmInstr`].
//! 
//! [`asm::AsmInstr`]: [`crate::ast::asm::AsmInstr`]

use std::ops::Range;

use crate::sim::SimErr;

use super::{CondCode, IOffset, ImmOrReg, Reg, TrapVect8};

const OP_BR: u16   = 0b0000; 
const OP_ADD: u16  = 0b0001; 
const OP_LD: u16   = 0b0010; 
const OP_ST: u16   = 0b0011; 
const OP_JSR: u16  = 0b0100; 
const OP_AND: u16  = 0b0101; 
const OP_LDR: u16  = 0b0110; 
const OP_STR: u16  = 0b0111; 
const OP_RTI: u16  = 0b1000; 
const OP_NOT: u16  = 0b1001; 
const OP_LDI: u16  = 0b1010; 
const OP_STI: u16  = 0b1011; 
const OP_JMP: u16  = 0b1100; 
const OP_LEA: u16  = 0b1110; 
const OP_TRAP: u16 = 0b1111; 

/// An enum representing all of the possible instructions in LC-3 bytecode.
/// 
/// The variants in this enum represent instructions after the both assembly passes.
/// There are no notions of aliases and labels in the variants in this enum.
/// 
/// For instructions that map to typeable assembly code, refer to [`asm::AsmInstr`].
/// 
/// [`asm::AsmInstr`]: [`crate::ast::asm::AsmInstr`]
#[derive(Debug, PartialEq, Eq, Hash, Clone, Copy)]
pub enum SimInstr {
    #[allow(missing_docs)]
    BR(CondCode, IOffset<9>),
    #[allow(missing_docs)]
    ADD(Reg, Reg, ImmOrReg<5>),
    #[allow(missing_docs)]
    LD(Reg, IOffset<9>),
    #[allow(missing_docs)]
    ST(Reg, IOffset<9>),
    #[allow(missing_docs)]
    JSR(ImmOrReg<11>),
    #[allow(missing_docs)]
    AND(Reg, Reg, ImmOrReg<5>),
    #[allow(missing_docs)]
    LDR(Reg, Reg, IOffset<6>),
    #[allow(missing_docs)]
    STR(Reg, Reg, IOffset<6>),
    #[allow(missing_docs)]
    RTI,
    #[allow(missing_docs)]
    NOT(Reg, Reg),
    #[allow(missing_docs)]
    LDI(Reg, IOffset<9>),
    #[allow(missing_docs)]
    STI(Reg, IOffset<9>),
    #[allow(missing_docs)]
    JMP(Reg),
    // Reserved,
    #[allow(missing_docs)]
    LEA(Reg, IOffset<9>),
    #[allow(missing_docs)]
    TRAP(TrapVect8),
}

impl SimInstr {
    /// Gets the opcode for the given instruction. This is always 4 bits.
    pub fn opcode(&self) -> u16 {
        match self {
            SimInstr::BR(_, _) => OP_BR,
            SimInstr::ADD(_, _, _) => OP_ADD,
            SimInstr::LD(_, _) => OP_LD,
            SimInstr::ST(_, _) => OP_ST,
            SimInstr::JSR(_) => OP_JSR,
            SimInstr::AND(_, _, _) => OP_AND,
            SimInstr::LDR(_, _, _) => OP_LDR,
            SimInstr::STR(_, _, _) => OP_STR,
            SimInstr::RTI => OP_RTI,
            SimInstr::NOT(_, _) => OP_NOT,
            SimInstr::LDI(_, _) => OP_LDI,
            SimInstr::STI(_, _) => OP_STI,
            SimInstr::JMP(_) => OP_JMP,
            // reserved => 0b1101
            SimInstr::LEA(_, _) => OP_LEA,
            SimInstr::TRAP(_) => OP_TRAP,
        }
    }

    /// Encodes this instruction as 16-bit bytecode.
    pub fn encode(&self) -> u16 {
        match self {
            SimInstr::BR(cc, off) => join_bits([
                (self.opcode(),    12..16),
                (*cc as u16,       9..12),
                (off.get() as u16, 0..9)
            ]),
            SimInstr::ADD(dr, sr1, ImmOrReg::Imm(i2)) => join_bits([ // ADD DR, SR1, imm5
                (self.opcode(),   12..16),
                (dr.0 as u16,     9..12),
                (sr1.0 as u16,    6..9),
                (0b1,             5..6),
                (i2.get() as u16, 0..5)
            ]),
            SimInstr::ADD(dr, sr1, ImmOrReg::Reg(r2)) => join_bits([ // ADD DR, SR1, SR2
                (self.opcode(), 12..16),
                (dr.0 as u16,   9..12),
                (sr1.0 as u16,  6..9),
                (0b000,         3..6),
                (r2.0 as u16,   0..3)
            ]),
            SimInstr::LD(dr, off) => join_bits([
                (self.opcode(),    12..16),
                (dr.0 as u16,      9..12),
                (off.get() as u16, 0..9)
            ]),
            SimInstr::ST(sr, off) => join_bits([
                (self.opcode(),    12..16),
                (sr.0 as u16,      9..12),
                (off.get() as u16, 0..9)
            ]),
            SimInstr::JSR(ImmOrReg::Imm(off)) => join_bits([ // JSR
                (self.opcode(),    12..16),
                (0b1,              11..12),
                (off.get() as u16, 0..11)
            ]),
            SimInstr::JSR(ImmOrReg::Reg(br)) => join_bits([ // JSRR
                (self.opcode(), 12..16),
                (0b000,         9..12),
                (br.0 as u16,   6..9),
                (0b000_000,     0..6)
            ]),
            SimInstr::AND(dr, sr1, ImmOrReg::Imm(i2)) => join_bits([ // AND DR, SR1, imm5
                (self.opcode(),   12..16),
                (dr.0 as u16,     9..12),
                (sr1.0 as u16,    6..9),
                (0b1,             5..6),
                (i2.get() as u16, 0..5)
            ]),
            SimInstr::AND(dr, sr1, ImmOrReg::Reg(r2)) => join_bits([ // AND DR, SR1, SR2
                (self.opcode(), 12..16),
                (dr.0 as u16,   9..12),
                (sr1.0 as u16,  6..9),
                (0b000,         3..6),
                (r2.0 as u16,   0..3)
            ]),
            SimInstr::LDR(dr, br, off) => join_bits([
                (self.opcode(),    12..16),
                (dr.0 as u16,      9..12),
                (br.0 as u16,      6..9),
                (off.get() as u16, 0..6)
            ]),
            SimInstr::STR(dr, br, off) => join_bits([
                (self.opcode(),    12..16),
                (dr.0 as u16,      9..12),
                (br.0 as u16,      6..9),
                (off.get() as u16, 0..6)
            ]),
            SimInstr::RTI => join_bits([
                (self.opcode(),    12..16),
                (0b0000_0000_0000, 0..12)
            ]),
            SimInstr::NOT(dr, sr) => join_bits([
                (self.opcode(), 12..16),
                (dr.0 as u16,   9..12),
                (sr.0 as u16,   6..9),
                (0b111_111,     0..6)
            ]),
            SimInstr::LDI(dr, off) => join_bits([
                (self.opcode(),    12..16),
                (dr.0 as u16,      9..12),
                (off.get() as u16, 0..9)
            ]),
            SimInstr::STI(sr, off) => join_bits([
                (self.opcode(),    12..16),
                (sr.0 as u16,      9..12),
                (off.get() as u16, 0..9)
            ]),
            SimInstr::JMP(br) => join_bits([
                (self.opcode(), 12..16),
                (0b000,         9..12),
                (br.0 as u16,   6..9),
                (0b000_000,     0..6)
            ]),
            SimInstr::LEA(dr, off) => join_bits([
                (self.opcode(),    12..16),
                (dr.0 as u16,      9..12),
                (off.get() as u16, 0..9)
            ]),
            SimInstr::TRAP(vect) => join_bits([
                (self.opcode(), 12..16),
                (0b0000,        8..12),
                (vect.get(),    0..8)
            ]),
        }
    }

    /// Converts a 16-bit bytecode representation into a `SimInstr`.
    /// This will error if the format is invalid.
    pub fn decode(word: u16) -> Result<Self, SimErr> {
        let opcode = get_bits(word, 12..16);
        match opcode {
            OP_BR => {
                let cc = get_bits(word, 9..12) as u8;
                let off = IOffset::new_trunc(get_bits(word, 0..9) as i16);
                Ok(Self::BR(cc, off))
            },
            OP_ADD => {
                let dr = Reg(get_bits(word, 9..12) as u8);
                let sr1 = Reg(get_bits(word, 6..9) as u8);
                let sr2 = match get_bits(word, 5..6) != 0 {
                    false => match get_bits(word, 3..5) == 0b00 {
                        true  => ImmOrReg::Reg(Reg(get_bits(word, 0..3) as u8)),
                        false => return Err(SimErr::InvalidInstrFormat)
                    },
                    true  => ImmOrReg::Imm(IOffset::new_trunc(get_bits(word, 0..5) as i16)),
                };

                Ok(Self::ADD(dr, sr1, sr2))
            },
            OP_LD => {
                let dr = Reg(get_bits(word, 9..12) as u8);
                let off = IOffset::new_trunc(get_bits(word, 0..9) as i16);

                Ok(Self::LD(dr, off))
            }
            OP_ST => {
                let sr = Reg(get_bits(word, 9..12) as u8);
                let off = IOffset::new_trunc(get_bits(word, 0..9) as i16);

                Ok(Self::ST(sr, off))
            },
            OP_JSR => {
                let val = match get_bits(word, 11..12) != 0 {
                    true  => ImmOrReg::Imm(IOffset::new_trunc(get_bits(word, 0..11) as i16)),
                    false => match get_bits(word, 9..11) == 0b00 && get_bits(word, 0..6) == 0b000_000 {
                        true  => ImmOrReg::Reg(Reg(get_bits(word, 6..9) as u8)),
                        false => return Err(SimErr::InvalidInstrFormat)
                    },
                };

                Ok(Self::JSR(val))
            },
            OP_AND => {
                let dr = Reg(get_bits(word, 9..12) as u8);
                let sr1 = Reg(get_bits(word, 6..9) as u8);
                let sr2 = match get_bits(word, 5..6) != 0 {
                    false => match get_bits(word, 3..5) == 0b00 {
                        true  => ImmOrReg::Reg(Reg(get_bits(word, 0..3) as u8)),
                        false => return Err(SimErr::InvalidInstrFormat)
                    },
                    true  => ImmOrReg::Imm(IOffset::new_trunc(get_bits(word, 0..5) as i16)),
                };

                Ok(Self::AND(dr, sr1, sr2))
            },
            OP_LDR => {
                let dr = Reg(get_bits(word, 9..12) as u8);
                let br = Reg(get_bits(word, 6..9) as u8);
                let off = IOffset::new_trunc(get_bits(word, 0..6) as i16);

                Ok(Self::LDR(dr, br, off))
            },
            OP_STR => {
                let sr = Reg(get_bits(word, 9..12) as u8);
                let br = Reg(get_bits(word, 6..9) as u8);
                let off = IOffset::new_trunc(get_bits(word, 0..6) as i16);

                Ok(Self::STR(sr, br, off))
            },
            OP_RTI => {
                match get_bits(word, 0..12) == 0b0000_0000_0000 {
                    true  => Ok(Self::RTI),
                    false => Err(SimErr::InvalidInstrFormat)
                }
            },
            OP_NOT => {
                let dr = Reg(get_bits(word, 9..12) as u8);
                let sr = Reg(get_bits(word, 6..9) as u8);

                match get_bits(word, 0..6) == 0b111_111 {
                    true  => Ok(Self::NOT(dr, sr)),
                    false => Err(SimErr::InvalidInstrFormat),
                }
            },
            OP_LDI => {
                let dr = Reg(get_bits(word, 9..12) as u8);
                let off = IOffset::new_trunc(get_bits(word, 0..9) as i16);

                Ok(Self::LDI(dr, off))
            },
            OP_STI => {
                let sr = Reg(get_bits(word, 9..12) as u8);
                let off = IOffset::new_trunc(get_bits(word, 0..9) as i16);

                Ok(Self::STI(sr, off))
            },
            OP_JMP => {
                let reg = match get_bits(word, 9..11) == 0b00 && get_bits(word, 0..6) == 0b000_000 {
                    true  => Reg(get_bits(word, 6..9) as u8),
                    false => return Err(SimErr::InvalidInstrFormat)
                };
                
                Ok(Self::JMP(reg))
            },
            OP_LEA => {
                let dr = Reg(get_bits(word, 9..12) as u8);
                let off = IOffset::new_trunc(get_bits(word, 0..9) as i16);

                Ok(Self::LEA(dr, off))
            },
            OP_TRAP => {
                let vect = match get_bits(word, 8..12) == 0b0000 {
                    true  => TrapVect8::new_trunc(get_bits(word, 0..8)),
                    false => return Err(SimErr::InvalidInstrFormat),
                };
                
                Ok(Self::TRAP(vect))
            },
            _ => Err(SimErr::InvalidOpcode)
        }
    }
}

/// Gets the bits of n within the range provided,
/// returning them as the least-significant bits
fn get_bits(n: u16, r: Range<usize>) -> u16 {
    let len = r.end - r.start;
    (n >> r.start) & ((1 << len) - 1)
}

/// Given a sequence of values and ranges, it writes each value into its corresponding range,
/// truncating the input value if it is too long.
fn join_bits<const N: usize>(bits: [(u16, Range<usize>); N]) -> u16 {
    bits.into_iter()
        .map(|(val, Range { start, end })| {
            let len = end - start;
            let mask = (1 << len) - 1;
            (val & mask) << start
        })
        .fold(0, std::ops::BitOr::bitor)
}