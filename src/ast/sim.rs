//! This module is used for holding simulation instructions,
//! which are instructions that directly map to bytecode
//! (as opposed to [todo_include_disp_instruction]) which
//! map to assembly code.

use std::ops::Range;

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

/// Instructions that map one-to-one to bytecode representation.
/// 
/// This erases all notions of aliases and labels.
/// For instructions that map to typeable assembly code, refer to [todo_include_disp_instruction].
pub enum SimInstr {
    #[allow(missing_docs)]
    Br(CondCode, IOffset<9>),
    #[allow(missing_docs)]
    Add(Reg, Reg, ImmOrReg<5>),
    #[allow(missing_docs)]
    Ld(Reg, IOffset<9>),
    #[allow(missing_docs)]
    St(Reg, IOffset<9>),
    #[allow(missing_docs)]
    Jsr(ImmOrReg<11>),
    #[allow(missing_docs)]
    And(Reg, Reg, ImmOrReg<5>),
    #[allow(missing_docs)]
    Ldr(Reg, Reg, IOffset<6>),
    #[allow(missing_docs)]
    Str(Reg, Reg, IOffset<6>),
    #[allow(missing_docs)]
    Rti,
    #[allow(missing_docs)]
    Not(Reg, Reg),
    #[allow(missing_docs)]
    Ldi(Reg, IOffset<9>),
    #[allow(missing_docs)]
    Sti(Reg, IOffset<9>),
    #[allow(missing_docs)]
    Jmp(Reg),
    // Reserved,
    #[allow(missing_docs)]
    Lea(Reg, IOffset<9>),
    #[allow(missing_docs)]
    Trap(TrapVect8),
}

impl SimInstr {
    /// Gets the opcode for the given instruction. This is always 4 bits.
    pub fn opcode(&self) -> u16 {
        match self {
            SimInstr::Br(_, _) => OP_BR,
            SimInstr::Add(_, _, _) => OP_ADD,
            SimInstr::Ld(_, _) => OP_LD,
            SimInstr::St(_, _) => OP_ST,
            SimInstr::Jsr(_) => OP_JSR,
            SimInstr::And(_, _, _) => OP_AND,
            SimInstr::Ldr(_, _, _) => OP_LDR,
            SimInstr::Str(_, _, _) => OP_STR,
            SimInstr::Rti => OP_RTI,
            SimInstr::Not(_, _) => OP_NOT,
            SimInstr::Ldi(_, _) => OP_LDI,
            SimInstr::Sti(_, _) => OP_STI,
            SimInstr::Jmp(_) => OP_JMP,
            // reserved => 0b1101
            SimInstr::Lea(_, _) => OP_LEA,
            SimInstr::Trap(_) => OP_TRAP,
        }
    }

    /// Encodes this instruction as 16-bit bytecode.
    pub fn encode(&self) -> u16 {
        match self {
            SimInstr::Br(cc, off) => join_bits([
                (self.opcode(),    12..16),
                (*cc as u16,       9..12),
                (off.get() as u16, 0..9)
            ]),
            SimInstr::Add(dr, sr1, ImmOrReg::Imm(i2)) => join_bits([ // ADD DR, SR1, imm5
                (self.opcode(),   12..16),
                (dr.0 as u16,     9..12),
                (sr1.0 as u16,    6..9),
                (0b1,             5..6),
                (i2.get() as u16, 0..5)
            ]),
            SimInstr::Add(dr, sr1, ImmOrReg::Reg(r2)) => join_bits([ // ADD DR, SR1, SR2
                (self.opcode(), 12..16),
                (dr.0 as u16,   9..12),
                (sr1.0 as u16,  6..9),
                (0b000,         3..6),
                (r2.0 as u16,   0..3)
            ]),
            SimInstr::Ld(dr, off) => join_bits([
                (self.opcode(),    12..16),
                (dr.0 as u16,      9..12),
                (off.get() as u16, 0..9)
            ]),
            SimInstr::St(sr, off) => join_bits([
                (self.opcode(),    12..16),
                (sr.0 as u16,      9..12),
                (off.get() as u16, 0..9)
            ]),
            SimInstr::Jsr(ImmOrReg::Imm(off)) => join_bits([ // JSR
                (self.opcode(),    12..16),
                (0b1,              11..12),
                (off.get() as u16, 0..11)
            ]),
            SimInstr::Jsr(ImmOrReg::Reg(br)) => join_bits([ // JSRR
                (self.opcode(), 12..16),
                (0b000,         9..12),
                (br.0 as u16,   6..9),
                (0b000_000,     0..6)
            ]),
            SimInstr::And(dr, sr1, ImmOrReg::Imm(i2)) => join_bits([ // AND DR, SR1, imm5
                (self.opcode(),   12..16),
                (dr.0 as u16,     9..12),
                (sr1.0 as u16,    6..9),
                (0b1,             5..6),
                (i2.get() as u16, 0..5)
            ]),
            SimInstr::And(dr, sr1, ImmOrReg::Reg(r2)) => join_bits([ // AND DR, SR1, SR2
                (self.opcode(), 12..16),
                (dr.0 as u16,   9..12),
                (sr1.0 as u16,  6..9),
                (0b000,         3..6),
                (r2.0 as u16,   0..3)
            ]),
            SimInstr::Ldr(dr, br, off) => join_bits([
                (self.opcode(),    12..16),
                (dr.0 as u16,      9..12),
                (br.0 as u16,      6..9),
                (off.get() as u16, 0..6)
            ]),
            SimInstr::Str(dr, br, off) => join_bits([
                (self.opcode(),    12..16),
                (dr.0 as u16,      9..12),
                (br.0 as u16,      6..9),
                (off.get() as u16, 0..6)
            ]),
            SimInstr::Rti => join_bits([
                (self.opcode(),    12..16),
                (0b0000_0000_0000, 0..12)
            ]),
            SimInstr::Not(dr, sr) => join_bits([
                (self.opcode(), 12..16),
                (dr.0 as u16,   9..12),
                (sr.0 as u16,   6..9),
                (0b111_111,     0..6)
            ]),
            SimInstr::Ldi(dr, off) => join_bits([
                (self.opcode(),    12..16),
                (dr.0 as u16,      9..12),
                (off.get() as u16, 0..9)
            ]),
            SimInstr::Sti(sr, off) => join_bits([
                (self.opcode(),    12..16),
                (sr.0 as u16,      9..12),
                (off.get() as u16, 0..9)
            ]),
            SimInstr::Jmp(br) => join_bits([
                (self.opcode(), 12..16),
                (0b000,         9..12),
                (br.0 as u16,   6..9),
                (0b000_000,     0..6)
            ]),
            SimInstr::Lea(dr, off) => join_bits([
                (self.opcode(),    12..16),
                (dr.0 as u16,      9..12),
                (off.get() as u16, 0..9)
            ]),
            SimInstr::Trap(vect) => join_bits([
                (self.opcode(), 12..16),
                (0b0000,        8..12),
                (vect.get(),    0..8)
            ]),
        }
    }

    /// Converts a 16-bit bytecode representation into a `SimInstr`.
    /// This will error if the format is invalid.
    pub fn decode(word: u16) -> Self {
        let (opcode, operands) = (word >> 4, (word << 4) >> 4);
        match opcode {
            OP_BR => {
                let cc = get_bits(operands, 9..12) as u8;
                let off = IOffset::new_trunc(get_bits(operands, 0..9) as i16);
                Self::Br(cc, off)
            },
            OP_ADD => {
                let dr = Reg(get_bits(operands, 9..12) as u8);
                let sr1 = Reg(get_bits(operands, 6..9) as u8);
                let sr2 = match get_bits(operands, 5..6) != 0 {
                    false => {
                        assert_eq!(get_bits(operands, 3..5), 0b00, "invalid instruction format"); // TODO: replace panic
                        ImmOrReg::Reg(Reg(get_bits(operands, 0..3) as u8))
                    },
                    true  => ImmOrReg::Imm(IOffset::new_trunc(get_bits(operands, 0..5) as i16)),
                };

                Self::Add(dr, sr1, sr2)
            },
            OP_LD => {
                let dr = Reg(get_bits(operands, 9..12) as u8);
                let off = IOffset::new_trunc(get_bits(operands, 0..9) as i16);

                Self::Ld(dr, off)
            }
            OP_ST => {
                let sr = Reg(get_bits(operands, 9..12) as u8);
                let off = IOffset::new_trunc(get_bits(operands, 0..9) as i16);

                Self::St(sr, off)
            },
            OP_JSR => {
                let val = match get_bits(operands, 11..12) != 0 {
                    true  => ImmOrReg::Imm(IOffset::new_trunc(get_bits(operands, 0..11) as i16)),
                    false => {
                        assert_eq!(get_bits(operands, 9..11), 0b00, "invalid instruction format"); // TODO: replace panic
                        assert_eq!(get_bits(operands, 0..6), 0b000000, "invalid instruction format"); // TODO: replace panic
                        ImmOrReg::Reg(Reg(get_bits(operands, 6..9) as u8))
                    },
                };

                Self::Jsr(val)
            },
            OP_AND => {
                let dr = Reg(get_bits(operands, 9..12) as u8);
                let sr1 = Reg(get_bits(operands, 6..9) as u8);
                let sr2 = match get_bits(operands, 5..6) != 0 {
                    false => {
                        assert_eq!(get_bits(operands, 3..5), 0b00, "invalid instruction format"); // TODO: replace panic
                        ImmOrReg::Reg(Reg(get_bits(operands, 0..3) as u8))
                    },
                    true  => ImmOrReg::Imm(IOffset::new_trunc(get_bits(operands, 0..5) as i16)),
                };

                Self::And(dr, sr1, sr2)
            },
            OP_LDR => {
                let dr = Reg(get_bits(operands, 9..12) as u8);
                let br = Reg(get_bits(operands, 6..9) as u8);
                let off = IOffset::new_trunc(get_bits(operands, 0..6) as i16);

                Self::Ldr(dr, br, off)
            },
            OP_STR => {
                let sr = Reg(get_bits(operands, 9..12) as u8);
                let br = Reg(get_bits(operands, 6..9) as u8);
                let off = IOffset::new_trunc(get_bits(operands, 0..6) as i16);

                Self::Str(sr, br, off)
            },
            OP_RTI => {
                assert_eq!(get_bits(operands, 0..12), 0b000000000000, "invalid instruction format"); // TODO: replace panic
                Self::Rti
            },
            OP_NOT => {
                let dr = Reg(get_bits(operands, 9..12) as u8);
                let sr = Reg(get_bits(operands, 6..9) as u8);
                assert_eq!(get_bits(operands, 0..6), 0b111111, "invalid instruction format"); // TODO: replace panic

                Self::Not(dr, sr)
            },
            OP_LDI => {
                let dr = Reg(get_bits(operands, 9..12) as u8);
                let off = IOffset::new_trunc(get_bits(operands, 0..9) as i16);

                Self::Ldi(dr, off)
            },
            OP_STI => {
                let sr = Reg(get_bits(operands, 9..12) as u8);
                let off = IOffset::new_trunc(get_bits(operands, 0..9) as i16);

                Self::Sti(sr, off)
            },
            OP_JMP => {
                assert_eq!(get_bits(operands, 9..12), 0b000, "invalid instruction format"); // TODO: replace panic
                let reg = Reg(get_bits(operands, 6..9) as u8);
                assert_eq!(get_bits(operands, 0..6), 0b000000, "invalid instruction format"); // TODO: replace panic
                
                Self::Jmp(reg)
            },
            OP_LEA => {
                let dr = Reg(get_bits(operands, 9..12) as u8);
                let off = IOffset::new_trunc(get_bits(operands, 0..9) as i16);

                Self::Lea(dr, off)
            },
            OP_TRAP => {
                assert_eq!(get_bits(operands, 8..12), 0b0000, "invalid instruction format"); // TODO: replace panic
                let vect = TrapVect8::new_trunc(get_bits(operands, 0..8));
                Self::Trap(vect)
            },
            _ => panic!("invalid opcode") // TODO: replace panic
        }
    }
}

/// Gets the bits of n within the range provided,
/// returning them as the least-significant bits
fn get_bits(n: u16, r: Range<usize>) -> u16 {
    let len = r.end - r.start;
    (n >> r.start) & ((1 << len) - 1)
}

fn join_bits<const N: usize>(bits: [(u16, Range<usize>); N]) -> u16 {
    bits.into_iter()
        .map(|(val, Range { start, end })| {
            let len = end - start;
            let mask = (1 << len) - 1;
            (val & mask) << start
        })
        .fold(0, std::ops::BitOr::bitor)
}