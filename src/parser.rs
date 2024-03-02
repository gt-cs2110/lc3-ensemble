use std::fmt::Write;

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
impl std::fmt::Display for Instruction {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Instruction::Add(dr, sr1, sr2) => write!(f, "ADD {dr}, {sr1}, {sr2}"),
            Instruction::And(dr, sr1, sr2) => write!(f, "AND {dr}, {sr1}, {sr2}"),
            Instruction::Not(dr, sr) => write!(f, "NOT {dr}, {sr}"),
            Instruction::Br(cc, off) => {
                write!(f, "BR")?;
                if cc & 0b100 != 0 { write!(f, "n")?; };
                if cc & 0b010 != 0 { write!(f, "z")?; };
                if cc & 0b001 != 0 { write!(f, "p")?; };
                write!(f, ", {off}")
            },
            Instruction::Jmp(br) => write!(f, "JMP {br}"),
            Instruction::Jsr(off) => write!(f, "JSR {off}"),
            Instruction::Jsrr(br) => write!(f, "JSRR {br}"),
            Instruction::Ld(dr, off) => write!(f, "LD {dr}, {off}"),
            Instruction::Ldi(dr, off) => write!(f, "LDI {dr}, {off}"),
            Instruction::Ldr(dr, br, off) => write!(f, "LDR {dr}, {br}, {off}"),
            Instruction::St(sr, off) => write!(f, "ST {sr}, {off}"),
            Instruction::Sti(sr, off) => write!(f, "STI {sr}, {off}"),
            Instruction::Str(sr, br, off) => write!(f, "STR {sr}, {br}, {off}"),
            Instruction::Trap(vect) => write!(f, "TRAP {vect:02X}"),
        }
    }
}

struct Reg(u8);
impl std::fmt::Display for Reg {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "R{}", self.0)
    }
}

type Imm5 = Offset<i16, 5>;
type CondCode = u8;
type Offset6 = Offset<i16, 6>;
type PCOffset9 = PCOffset<i16, 9>;
type PCOffset11 = PCOffset<i16, 11>;
type TrapVect8 = Offset<u16, 8>;

enum ImmOrReg {
    Imm(Imm5),
    Reg(Reg)
}
impl std::fmt::Display for ImmOrReg {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ImmOrReg::Imm(imm) => imm.fmt(f),
            ImmOrReg::Reg(reg) => reg.fmt(f),
        }
    }
}

struct Offset<OFF, const N: usize>(OFF);

impl<const N: usize> Offset<u16, N> {
    fn new(n: u16) -> Result<Self, ParseErr> {
        match n == (n << (16 - N)) >> (16 - N) {
            true  => Ok(Offset(n)),
            false => Err(ParseErr { msg: "value is too big for unsigned 16-bit integer" }),
        }
    }
}
impl<const N: usize> Offset<i16, N> {
    fn new(n: i16) -> Result<Self, ParseErr> {
        match n == (n << (16 - N)) >> (16 - N) {
            true  => Ok(Offset(n)),
            false => Err(ParseErr { msg: "value is too big for signed 16-bit integer" }),
        }
    }
}

impl<OFF: std::fmt::Display, const N: usize> std::fmt::Display for Offset<OFF, N> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_char('#')?;
        self.0.fmt(f)
    }
}
impl<const N: usize> std::fmt::Binary for Offset<u16, N> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_char('b')?;
        self.0.fmt(f)
    }
}
impl<const N: usize> std::fmt::LowerHex for Offset<u16, N> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_char('x')?;
        self.0.fmt(f)
    }
}
impl<const N: usize> std::fmt::UpperHex for Offset<u16, N> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_char('x')?;
        self.0.fmt(f)
    }
}

enum PCOffset<OFF, const N: usize> {
    Offset(Offset<OFF, N>),
    Label(String)
}
impl<OFF, const N: usize> std::fmt::Display for PCOffset<OFF, N> 
    where Offset<OFF, N>: std::fmt::Display
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            PCOffset::Offset(off)  => off.fmt(f),
            PCOffset::Label(label) => label.fmt(f),
        }
    }
}

struct ParseErr {
    msg: &'static str
}

trait Parse: Sized {
    fn parse(parser: &mut Parser<'_>) -> Result<Self, ParseErr>;
}

struct Parser<'s> {
    tokens: &'s [(Token, Span)]
}
impl Parser<'_> {
    fn peek(&self) -> Option<&(Token, Span)> {
        self.tokens.first()
    }

    fn parse<P: Parse>(&mut self) -> Result<P, ParseErr> {
        P::parse(self)
    }
    fn match_<T>(&mut self, pred: impl FnOnce(&Token) -> Result<T, ParseErr>) -> Result<T, ParseErr> {
        let Some((tok, _)) = self.peek() else { return Err(ParseErr { msg: "unexpected eol" }) };
        
        let result = pred(tok);
        if result.is_ok() {
            self.next();
        }
        result
    }
}
impl<'s> Iterator for Parser<'s> {
    type Item = &'s (Token, Span);

    fn next(&mut self) -> Option<Self::Item> {
        let (first, rest) = self.tokens.split_first()?;
        self.tokens = rest;
        Some(first)
    }
}
impl Parse for Reg {
    fn parse(parser: &mut Parser<'_>) -> Result<Self, ParseErr> {
        parser.match_(|t| match t {
            &Token::Reg(reg) => Ok(Reg(reg)),
            _ => Err(ParseErr { msg: "expected register" }),
        })
    }
}
impl<const N: usize> Parse for Offset<u16, N> {
    fn parse(parser: &mut Parser<'_>) -> Result<Self, ParseErr> {
        parser.match_(|t| match t {
            &Token::Numeric(n) => Self::new(n),
            _ => Err(ParseErr { msg: "expected register" }),
        })
    }
}
impl<const N: usize> Parse for Offset<i16, N> {
    fn parse(parser: &mut Parser<'_>) -> Result<Self, ParseErr> {
        parser.match_(|t| match t {
            &Token::Numeric(n) => Self::new(n as _),
            _ => Err(ParseErr { msg: "expected register" }),
        })
    }
}
impl<const N: usize> Parse for PCOffset<u16, N> {
    fn parse(parser: &mut Parser<'_>) -> Result<Self, ParseErr> {
        match parser.parse() {
            Ok(off) => Ok(PCOffset::Offset(off)),
            Err(_) => parser.match_(|t| match t {
                Token::Ident(s) => Ok(PCOffset::Label(s.to_string())),
                _ => Err(ParseErr { msg: "expected offset or label" })
            }),
        }
    }
}
impl<const N: usize> Parse for PCOffset<i16, N> {
    fn parse(parser: &mut Parser<'_>) -> Result<Self, ParseErr> {
        match parser.parse() {
            Ok(off) => Ok(PCOffset::Offset(off)),
            Err(_) => parser.match_(|t| match t {
                Token::Ident(s) => Ok(PCOffset::Label(s.to_string())),
                _ => Err(ParseErr { msg: "expected offset or label" })
            }),
        }
    }
}
impl Parse for ImmOrReg {
    fn parse(parser: &mut Parser<'_>) -> Result<Self, ParseErr> {
        match parser.parse() {
            Ok(imm) => Ok(ImmOrReg::Imm(imm)),
            Err(_) => match parser.parse() {
                Ok(reg) => Ok(ImmOrReg::Reg(reg)),
                Err(_) => Err(ParseErr { msg: "expected immediate value or register" }),
            }
        }
    }
}
impl Parse for Instruction {
    fn parse(parser: &mut Parser<'_>) -> Result<Self, ParseErr> {
        let opcode = parser.match_(|t| match t {
            Token::Numeric(_) => Err(ParseErr { msg: "unexpected numeric" }),
            Token::Reg(_) => Err(ParseErr { msg: "unexpected register" }),
            Token::Ident(id) => Ok(id.to_string()),
            Token::Directive(_) => Err(ParseErr { msg: "unexpected directive" }),
            Token::Colon => Err(ParseErr { msg: "unexpected colon" }),
            Token::Comma => Err(ParseErr { msg: "unexpected comma" }),
            Token::Comment => Err(ParseErr { msg: "unexpected comment" }), // FIXME
        })?;

        match &*opcode.to_uppercase() {
            "ADD" => {
                let dr = parser.parse()?;
                parser.match_(|t| if let Token::Comma = t { Ok(()) } else { Err(ParseErr { msg: "expected comma" }) })?;
                let sr1 = parser.parse()?;
                parser.match_(|t| if let Token::Comma = t { Ok(()) } else { Err(ParseErr { msg: "expected comma" }) })?;
                let sr2 = parser.parse()?;

                Ok(Self::Add(dr, sr1, sr2))
            },
            "AND" => {
                let dr = parser.parse()?;
                parser.match_(|t| if let Token::Comma = t { Ok(()) } else { Err(ParseErr { msg: "expected comma" }) })?;
                let sr1 = parser.parse()?;
                parser.match_(|t| if let Token::Comma = t { Ok(()) } else { Err(ParseErr { msg: "expected comma" }) })?;
                let sr2 = parser.parse()?;

                Ok(Self::And(dr, sr1, sr2))
            },
            "NOT" => {
                let dr = parser.parse()?;
                parser.match_(|t| if let Token::Comma = t { Ok(()) } else { Err(ParseErr { msg: "expected comma" }) })?;
                let sr = parser.parse()?;

                Ok(Self::Not(dr, sr))
            },
            "BR" => Ok(Self::Br(0b111, parser.parse()?)),
            "BRP" => Ok(Self::Br(0b001, parser.parse()?)),
            "BRZ" => Ok(Self::Br(0b010, parser.parse()?)),
            "BRZP" => Ok(Self::Br(0b011, parser.parse()?)),
            "BRN" => Ok(Self::Br(0b100, parser.parse()?)),
            "BRNP" => Ok(Self::Br(0b101, parser.parse()?)),
            "BRNZ" => Ok(Self::Br(0b110, parser.parse()?)),
            "BRNZP" => Ok(Self::Br(0b111, parser.parse()?)),
            "JMP" => Ok(Self::Jmp(parser.parse()?)),
            "JSR" => Ok(Self::Jsr(parser.parse()?)),
            "JSRR" => Ok(Self::Jsrr(parser.parse()?)),
            "LD" => {
                let dr = parser.parse()?;
                parser.match_(|t| if let Token::Comma = t { Ok(()) } else { Err(ParseErr { msg: "expected comma" }) })?;
                let off = parser.parse()?;

                Ok(Self::Ld(dr, off))
            },
            "LDI" => {
                let dr = parser.parse()?;
                parser.match_(|t| if let Token::Comma = t { Ok(()) } else { Err(ParseErr { msg: "expected comma" }) })?;
                let off = parser.parse()?;

                Ok(Self::Ldi(dr, off))
            },
            "LDR" => {
                let dr = parser.parse()?;
                parser.match_(|t| if let Token::Comma = t { Ok(()) } else { Err(ParseErr { msg: "expected comma" }) })?;
                let br = parser.parse()?;
                parser.match_(|t| if let Token::Comma = t { Ok(()) } else { Err(ParseErr { msg: "expected comma" }) })?;
                let off = parser.parse()?;

                Ok(Self::Ldr(dr, br, off))
            },
            "ST" => {
                let sr = parser.parse()?;
                parser.match_(|t| if let Token::Comma = t { Ok(()) } else { Err(ParseErr { msg: "expected comma" }) })?;
                let off = parser.parse()?;

                Ok(Self::St(sr, off))
            },
            "STI" => {
                let sr = parser.parse()?;
                parser.match_(|t| if let Token::Comma = t { Ok(()) } else { Err(ParseErr { msg: "expected comma" }) })?;
                let off = parser.parse()?;

                Ok(Self::Sti(sr, off))
            },
            "STR" => {
                let dr = parser.parse()?;
                parser.match_(|t| if let Token::Comma = t { Ok(()) } else { Err(ParseErr { msg: "expected comma" }) })?;
                let br = parser.parse()?;
                parser.match_(|t| if let Token::Comma = t { Ok(()) } else { Err(ParseErr { msg: "expected comma" }) })?;
                let off = parser.parse()?;

                Ok(Self::Str(dr, br, off))
            },
            "TRAP" => Ok(Self::Trap(parser.parse()?)),
            _ => Err(ParseErr { msg: "invalid instruction" })
        }
    }
}