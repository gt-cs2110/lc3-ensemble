//! This module is used for holding simulation instructions ([`Self`]),
//! which are instructions that directly map to assembly code.
//! 
//! For instructions that map bytecode, see [`sim::SimInstr`].
//! 
//! [`sim::SimInstr`]: [`crate::ast::sim::SimInstr`]

use std::fmt::Write as _;

use super::{CondCode, IOffset, ImmOrReg, Offset, PCOffset, Reg, TrapVect8};


type PCOffset9 = PCOffset<i16, 9>;
type PCOffset11 = PCOffset<i16, 11>;

pub enum AsmInstr {
    ADD(Reg, Reg, ImmOrReg<5>),
    AND(Reg, Reg, ImmOrReg<5>),
    NOT(Reg, Reg),
    BR(CondCode, PCOffset9),
    JMP(Reg),
    JSR(PCOffset11),
    JSRR(Reg),
    LD(Reg, PCOffset9),
    LDI(Reg, PCOffset9),
    LDR(Reg, Reg, IOffset<6>),
    LEA(Reg, PCOffset9),
    ST(Reg, PCOffset9),
    STI(Reg, PCOffset9),
    STR(Reg, Reg, IOffset<6>),
    TRAP(TrapVect8),

    // Extra instructions
    NOP,
    RET,
    RTI,
    GETC,
    OUT,
    PUTC,
    PUTS,
    IN,
    PUTSP,
    HALT
}
impl std::fmt::Display for AsmInstr {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::ADD(dr, sr1, sr2) => write!(f, "ADD {dr}, {sr1}, {sr2}"),
            Self::AND(dr, sr1, sr2) => write!(f, "AND {dr}, {sr1}, {sr2}"),
            Self::NOT(dr, sr) => write!(f, "NOT {dr}, {sr}"),
            Self::BR(cc, off) => {
                write!(f, "BR")?;
                if cc & 0b100 != 0 { f.write_char('n')?; };
                if cc & 0b010 != 0 { f.write_char('z')?; };
                if cc & 0b001 != 0 { f.write_char('p')?; };
                write!(f, ", {off}")
            },
            Self::JMP(br) => write!(f, "JMP {br}"),
            Self::JSR(off) => write!(f, "JSR {off}"),
            Self::JSRR(br) => write!(f, "JSRR {br}"),
            Self::LD(dr, off) => write!(f, "LD {dr}, {off}"),
            Self::LDI(dr, off) => write!(f, "LDI {dr}, {off}"),
            Self::LDR(dr, br, off) => write!(f, "LDR {dr}, {br}, {off}"),
            Self::LEA(dr, off) => write!(f, "LEA {dr}, {off}"),
            Self::ST(sr, off) => write!(f, "ST {sr}, {off}"),
            Self::STI(sr, off) => write!(f, "STI {sr}, {off}"),
            Self::STR(sr, br, off) => write!(f, "STR {sr}, {br}, {off}"),
            Self::TRAP(vect) => write!(f, "TRAP {vect:02X}"),
            Self::NOP   => f.write_str("NOP"),
            Self::RET   => f.write_str("RET"),
            Self::RTI   => f.write_str("RTI"),
            Self::GETC  => f.write_str("GETC"),
            Self::OUT   => f.write_str("OUT"),
            Self::PUTC  => f.write_str("PUTC"),
            Self::PUTS  => f.write_str("PUTS"),
            Self::IN    => f.write_str("IN"),
            Self::PUTSP => f.write_str("PUTSP"),
            Self::HALT  => f.write_str("HALT"),
        }
    }
}

pub enum Directive {
    Orig(Offset<u16, 16>),
    Fill(PCOffset<u16, 16>),
    Blkw(Offset<u16, 16>),
    Stringz(String),
    End,
    // External
}
impl std::fmt::Display for Directive {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Orig(addr)   => write!(f, ".orig {addr:04x}"),
            Self::Fill(val)    => write!(f, ".fill {val}"),
            Self::Blkw(n)      => write!(f, ".blkw {n}"),
            Self::Stringz(val) => write!(f, ".stringz {val:?}"),
            Self::End          => write!(f, ".end"),
        }
    }
}
enum StmtKind {
    Instr(AsmInstr),
    Directive(Directive)
}
struct Stmt {
    labels: Vec<String>,
    nucleus: StmtKind
}