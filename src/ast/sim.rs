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

pub enum SimInstr {
    Br(CondCode, IOffset<9>),
    Add(Reg, Reg, ImmOrReg<5>),
    Ld(Reg, IOffset<9>),
    St(Reg, IOffset<9>),
    Jsr(ImmOrReg<11>),
    And(Reg, Reg, ImmOrReg<5>),
    Ldr(Reg, Reg, IOffset<6>),
    Str(Reg, Reg, IOffset<6>),
    Rti,
    Not(Reg, Reg),
    Ldi(Reg, IOffset<9>),
    Sti(Reg, IOffset<9>),
    Jmp(Reg),
    // Reserved,
    Lea(Reg, IOffset<9>),
    Trap(TrapVect8),
}

impl SimInstr {
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
    pub fn encode(&self) -> u16 {
        match self {
            SimInstr::Br(cc, off)       => (self.opcode() << 12) | ((*cc as u16 & 0b111) << 9) | off.repr(),
            SimInstr::Add(dr, sr1, sr2) => match sr2 {
                ImmOrReg::Imm(i2) => (self.opcode() << 12) | ((dr.0 as u16) << 9) | ((sr1.0 as u16) << 6) | (1 << 5) | i2.repr(),
                ImmOrReg::Reg(r2) => (self.opcode() << 12) | ((dr.0 as u16) << 9) | ((sr1.0 as u16) << 6) | (r2.0 as u16),
            },
            SimInstr::Ld(dr, off)       => (self.opcode() << 12) | ((dr.0 as u16) << 9) | off.repr(),
            SimInstr::St(sr, off)       => (self.opcode() << 12) | ((sr.0 as u16) << 9) | off.repr(),
            SimInstr::Jsr(arg)          => match arg {
                ImmOrReg::Imm(o) => (self.opcode() << 12) | (1 << 11) | o.repr(),
                ImmOrReg::Reg(r) => (self.opcode() << 12) | (r.0 as u16) << 6,
            }
            SimInstr::And(dr, sr1, sr2) => match sr2 {
                ImmOrReg::Imm(i2) => (self.opcode() << 12) | ((dr.0 as u16) << 9) | ((sr1.0 as u16) << 6) | (1 << 5) | i2.repr(),
                ImmOrReg::Reg(r2) => (self.opcode() << 12) | ((dr.0 as u16) << 9) | ((sr1.0 as u16) << 6) | (r2.0 as u16),
            },
            SimInstr::Ldr(dr, br, off)  => (self.opcode() << 12) | ((dr.0 as u16) << 9) | ((br.0 as u16) << 6) | off.repr(),
            SimInstr::Str(sr, br, off)  => (self.opcode() << 12) | ((sr.0 as u16) << 9) | ((br.0 as u16) << 6) | off.repr(),
            SimInstr::Rti               => self.opcode() << 12,
            SimInstr::Not(dr, sr)       => (self.opcode() << 12) | ((dr.0 as u16) << 9) | ((sr.0 as u16) << 6) | 0b111111,
            SimInstr::Ldi(dr, off)      => (self.opcode() << 12) | ((dr.0 as u16) << 9) | off.repr(),
            SimInstr::Sti(sr, off)      => (self.opcode() << 12) | ((sr.0 as u16) << 9) | off.repr(),
            SimInstr::Jmp(br)           => (self.opcode() << 12) | (br.0 as u16) << 6,
            SimInstr::Lea(dr, off)      => (self.opcode() << 12) | ((dr.0 as u16) << 9) | off.repr(),
            SimInstr::Trap(vect)        => (self.opcode() << 12) | vect.repr(),
        }
    }

    pub fn decode(word: u16) -> Self {
        let (opcode, operands) = (word >> 4, (word << 4) >> 4);
        match opcode {
            OP_BR => {
                let cc = get_bits(operands, 9..12) as u8;
                let off = IOffset::new_trunc(get_bits(operands, 0..9) as i16);
                Self::Br(cc, off)
            },
            OP_ADD => todo!("OP_ADD"),
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
            OP_JSR => todo!("OP_JSR"),
            OP_AND => todo!("OP_AND"),
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
            OP_RTI => todo!("OP_RTI"),
            OP_NOT => todo!("OP_NOT"),
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
            OP_JMP => todo!("OP_JMP"),
            OP_LEA => {
                let dr = Reg(get_bits(operands, 9..12) as u8);
                let off = IOffset::new_trunc(get_bits(operands, 0..9) as i16);

                Self::Lea(dr, off)
            },
            OP_TRAP => todo!("OP_TRAP"),
            _ => panic!("invalid opcode") // FIXME
        }
    }
}

fn get_bits(n: u16, r: std::ops::Range<usize>) -> u16 {
    let len = r.end - r.start;
    (n >> r.start) & ((1 << len) - 1)
}