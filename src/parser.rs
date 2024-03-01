use logos::Span;

use crate::lexer::Token;

enum Instruction {
    Add(Reg, Reg, ImmOrReg),
    And(Reg, Reg, ImmOrReg),
    Not(Reg, Reg),
    Br(CondCode, PCOffset9),
    Jmp(Reg),
    Jsr(PCOffset11),
    Jsrr(Reg),
    Ld(Reg, PCOffset9),
    Ldi(Reg, PCOffset9),
    Ldr(Reg, Reg, Offset6),
    St(Reg, PCOffset9),
    Sti(Reg, PCOffset9),
    Str(Reg, Reg, Offset6),
    Trap(TrapVect8)
}

type Reg = u8;
type Imm5 = i8;
type CondCode = u8;
type PCOffset9 = PCOffset<i16>;
type PCOffset11 = PCOffset<i16>;
type Offset6 = i8;
type TrapVect8 = u8;

enum ImmOrReg {
    Imm(Imm5),
    Reg(Reg)
}
impl std::fmt::Display for ImmOrReg {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ImmOrReg::Imm(imm) => write!(f, "#{imm}"),
            ImmOrReg::Reg(reg) => write!(f, "R{reg}"),
        }
    }
}
enum PCOffset<OFF> {
    Offset(OFF),
    Label(String)
}
impl<T: std::fmt::Display> std::fmt::Display for PCOffset<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            PCOffset::Offset(off) => write!(f, "#{off}"),
            PCOffset::Label(label) => label.fmt(f),
        }
    }
}

impl std::fmt::Display for Instruction {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Instruction::Add(dr, sr1, sr2) => write!(f, "ADD R{dr}, R{sr1}, {sr2}"),
            Instruction::And(dr, sr1, sr2) => write!(f, "AND R{dr}, R{sr1}, {sr2}"),
            Instruction::Not(dr, sr)    => write!(f, "NOT {dr}, {sr}"),
            Instruction::Br(cc, off)     => {
                write!(f, "BR")?;
                if cc & 0b100 != 0 { write!(f, "n")?; };
                if cc & 0b010 != 0 { write!(f, "z")?; };
                if cc & 0b001 != 0 { write!(f, "p")?; };
                write!(f, ", {off}")
            },
            Instruction::Jmp(br)      => write!(f, "JMP R{br}"),
            Instruction::Jsr(off)     => write!(f, "JSR {off}"),
            Instruction::Jsrr(br)     => write!(f, "JSRR R{br}"),
            Instruction::Ld(dr, off)     => write!(f, "LD R{dr}, {off}"),
            Instruction::Ldi(dr, off)    => write!(f, "LDI R{dr}, {off}"),
            Instruction::Ldr(dr, br, off) => write!(f, "LDR R{dr}, R{br}, #{off}"),
            Instruction::St(sr, off)     => write!(f, "ST R{sr}, {off}"),
            Instruction::Sti(sr, off)    => write!(f, "STI R{sr}, {off}"),
            Instruction::Str(sr, br, off) => write!(f, "STR R{sr}, R{br}, #{off}"),
            Instruction::Trap(vect)   => write!(f, "TRAP x{vect:02X}"),
        }
    }
}

enum ParseErr {
    ExpectedReg,
    ExpectedNumeric,
    ExpectedPCOffset,
    ExpectedComma,
    ExpectedColon,
    ExpectedImmOrReg
}

trait Parse: Sized {
    fn parse(stream: &mut Parser<'_>) -> Result<Self, ParseErr>;
}

struct Parser<'s> {
    tokens: &'s [(Token, Span)]
}
impl Parser<'_> {
    fn parse<P: Parse>(&mut self) -> Result<P, ParseErr> {
        P::parse(self)
    }

    fn expect_reg(&mut self) -> Result<Reg, ParseErr> {
        self.match_reg()
            .ok_or(ParseErr::ExpectedReg)
    }
    fn expect_numeric(&mut self) -> Result<u16, ParseErr> {
        self.match_numeric()
            .ok_or(ParseErr::ExpectedNumeric)
    }
    fn expect_pc_offset(&mut self) -> Result<PCOffset<i16>, ParseErr> {
        self.match_pc_offset()
            .ok_or(ParseErr::ExpectedPCOffset)
    }
    fn expect_colon(&mut self) -> Result<(), ParseErr> {
        match self.match_colon() {
            true  => Ok(()),
            false => Err(ParseErr::ExpectedColon),
        }
    }
    fn expect_comma(&mut self) -> Result<(), ParseErr> {
        match self.match_comma() {
            true  => Ok(()),
            false => Err(ParseErr::ExpectedComma),
        }
    }

    fn match_reg(&mut self) -> Option<Reg> {
        if let Some((&(Token::Reg(reg), _), rest)) = self.tokens.split_first() {
            self.tokens = rest;
            return Some(reg);
        }

        None
    }
    fn match_numeric(&mut self) -> Option<u16> {
        if let Some((&(Token::Numeric(num), _), rest)) = self.tokens.split_first() {
            self.tokens = rest;
            return Some(num);
        }

        None
    }
    fn match_pc_offset(&mut self) -> Option<PCOffset<i16>> {
        if let Some(((first_tok, _), rest)) = self.tokens.split_first() {
            match first_tok {
                &Token::Numeric(num) => {
                    self.tokens = rest;
                    return Some(PCOffset::Offset(num as i16))
                },
                Token::Ident(id) => {
                    self.tokens = rest;
                    return Some(PCOffset::Label(id.to_string()))
                },
                _ => {}
            }
        }

        None
    }
    fn match_colon(&mut self) -> bool {
        if let Some(((Token::Colon, _), rest)) = self.tokens.split_first() {
            self.tokens = rest;
            return true;
        }

        false
    }
    fn match_comma(&mut self) -> bool {
        if let Some(((Token::Comma, _), rest)) = self.tokens.split_first() {
            self.tokens = rest;
            return true;
        }

        false
    }
}
impl Parse for ImmOrReg {
    fn parse(stream: &mut Parser<'_>) -> Result<Self, ParseErr> {
        if let Some(num) = stream.match_numeric() {
            return Ok(ImmOrReg::Imm(num as i8));
        }

        if let Some(reg) = stream.match_reg() {
            return Ok(ImmOrReg::Reg(reg));
        }

        Err(ParseErr::ExpectedImmOrReg)
    }
}
impl Parse for PCOffset<i16> {
    fn parse(stream: &mut Parser<'_>) -> Result<Self, ParseErr> {
        stream.expect_pc_offset()
    }
}