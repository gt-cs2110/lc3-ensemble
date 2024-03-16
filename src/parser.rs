//! Parser that converts tokens from an LC-3 assembly file into
//! an AST.

use std::borrow::Cow;

use logos::Span;

use crate::ast::{CondCode, IOffset, ImmOrReg, Offset, PCOffset, Reg, TrapVect8};
use crate::lexer::{Ident, Token};

type PCOffset9 = PCOffset<i16, 9>;
type PCOffset11 = PCOffset<i16, 11>;

enum Instruction {
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

impl std::fmt::Display for Instruction {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Instruction::ADD(dr, sr1, sr2) => write!(f, "ADD {dr}, {sr1}, {sr2}"),
            Instruction::AND(dr, sr1, sr2) => write!(f, "AND {dr}, {sr1}, {sr2}"),
            Instruction::NOT(dr, sr) => write!(f, "NOT {dr}, {sr}"),
            Instruction::BR(cc, off) => {
                write!(f, "BR")?;
                if cc & 0b100 != 0 { write!(f, "n")?; };
                if cc & 0b010 != 0 { write!(f, "z")?; };
                if cc & 0b001 != 0 { write!(f, "p")?; };
                write!(f, ", {off}")
            },
            Instruction::JMP(br) => write!(f, "JMP {br}"),
            Instruction::JSR(off) => write!(f, "JSR {off}"),
            Instruction::JSRR(br) => write!(f, "JSRR {br}"),
            Instruction::LD(dr, off) => write!(f, "LD {dr}, {off}"),
            Instruction::LDI(dr, off) => write!(f, "LDI {dr}, {off}"),
            Instruction::LDR(dr, br, off) => write!(f, "LDR {dr}, {br}, {off}"),
            Instruction::LEA(dr, off) => write!(f, "LEA {dr}, {off}"),
            Instruction::ST(sr, off) => write!(f, "ST {sr}, {off}"),
            Instruction::STI(sr, off) => write!(f, "STI {sr}, {off}"),
            Instruction::STR(sr, br, off) => write!(f, "STR {sr}, {br}, {off}"),
            Instruction::TRAP(vect) => write!(f, "TRAP {vect:02X}"),
            Instruction::NOP   => f.write_str("NOP"),
            Instruction::RET   => f.write_str("RET"),
            Instruction::RTI   => f.write_str("RTI"),
            Instruction::GETC  => f.write_str("GETC"),
            Instruction::OUT   => f.write_str("OUT"),
            Instruction::PUTC  => f.write_str("PUTC"),
            Instruction::PUTS  => f.write_str("PUTS"),
            Instruction::IN    => f.write_str("IN"),
            Instruction::PUTSP => f.write_str("PUTSP"),
            Instruction::HALT  => f.write_str("HALT"),
        }
    }
}

enum Directive {
    Orig(Offset<u16, 16>),
    Fill(Offset<u16, 16>),
    Blkw(Offset<u16, 16>),
    Stringz(String),
    End,
    // External
}

struct ParseErr {
    msg: Cow<'static, str>
}
impl ParseErr {
    fn new<C: Into<Cow<'static, str>>>(msg: C) -> Self {
        Self { msg: msg.into() }
    }
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
        let Some((tok, _)) = self.peek() else { return Err(ParseErr::new("unexpected eol")) };
        
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
            _ => Err(ParseErr::new("expected register")),
        })
    }
}
impl<const N: u32> Parse for ImmOrReg<N> {
    fn parse(parser: &mut Parser<'_>) -> Result<Self, ParseErr> {
        match parser.parse() {
            Ok(imm) => Ok(ImmOrReg::Imm(imm)),
            Err(_) => match parser.parse() {
                Ok(reg) => Ok(ImmOrReg::Reg(reg)),
                Err(_) => Err(ParseErr::new("expected immediate value or register")),
            }
        }
    }
}

impl<const N: u32> Parse for Offset<i16, N> {
    fn parse(parser: &mut Parser<'_>) -> Result<Self, ParseErr> {
        parser.match_(|t| {
            let off_val = match *t {
                Token::Unsigned(n) => i16::try_from(n).map_err(|_| todo!("impl lex error if overflow")),
                Token::Signed(n) => Ok(n),
                _ => Err(ParseErr::new("expected immediate value"))
            }?;
            
            Self::new(off_val)
                .map_err(|s| ParseErr::new(s.to_string()))
        })
    }
}
impl<const N: u32> Parse for Offset<u16, N> {
    fn parse(parser: &mut Parser<'_>) -> Result<Self, ParseErr> {
        parser.match_(|t| {
            let off_val = match *t {
                Token::Unsigned(n) => Ok(n),
                Token::Signed(n) => u16::try_from(n).map_err(|_| todo!("impl lex error if overflow")),
                _ => Err(ParseErr::new("expected immediate value"))
            }?;
            
            Self::new(off_val)
                .map_err(|s| ParseErr::new(s.to_string()))
        })
    }
}

impl<OFF, const N: u32> Parse for PCOffset<OFF, N> 
    where Offset<OFF, N>: Parse
{
    fn parse(parser: &mut Parser<'_>) -> Result<Self, ParseErr> {
        match parser.parse() {
            Ok(off) => Ok(PCOffset::Offset(off)),
            Err(_) => parser.match_(|t| match t {
                Token::Ident(Ident::Label(s)) => Ok(PCOffset::Label(s.to_string())),
                _ => Err(ParseErr::new("expected offset or label"))
            }),
        }
    }
}

fn parse_comma(t: &Token) -> Result<(), ParseErr> {
    match t {
        Token::Comma => Ok(()),
        _ => Err(ParseErr::new("expected comma"))
    }
}

impl Parse for Instruction {
    fn parse(parser: &mut Parser<'_>) -> Result<Self, ParseErr> {
        let opcode = parser.match_(|t| match t {
            Token::Ident(Ident::Label(_)) => Err(ParseErr::new("expected instruction")),
            Token::Ident(id) => Ok(id.clone()),
            _ => Err(ParseErr::new("expected instruction"))
        })?;

        match opcode {
            Ident::ADD => {
                let dr = parser.parse()?;
                parser.match_(parse_comma)?;
                let sr1 = parser.parse()?;
                parser.match_(parse_comma)?;
                let sr2 = parser.parse()?;

                Ok(Self::ADD(dr, sr1, sr2))
            },
            Ident::AND => {
                let dr = parser.parse()?;
                parser.match_(parse_comma)?;
                let sr1 = parser.parse()?;
                parser.match_(parse_comma)?;
                let sr2 = parser.parse()?;

                Ok(Self::AND(dr, sr1, sr2))
            },
            Ident::NOT => {
                let dr = parser.parse()?;
                parser.match_(parse_comma)?;
                let sr = parser.parse()?;

                Ok(Self::NOT(dr, sr))
            },
            Ident::BR => Ok(Self::BR(0b111, parser.parse()?)),
            Ident::BRP => Ok(Self::BR(0b001, parser.parse()?)),
            Ident::BRZ => Ok(Self::BR(0b010, parser.parse()?)),
            Ident::BRZP => Ok(Self::BR(0b011, parser.parse()?)),
            Ident::BRN => Ok(Self::BR(0b100, parser.parse()?)),
            Ident::BRNP => Ok(Self::BR(0b101, parser.parse()?)),
            Ident::BRNZ => Ok(Self::BR(0b110, parser.parse()?)),
            Ident::BRNZP => Ok(Self::BR(0b111, parser.parse()?)),
            Ident::JMP => Ok(Self::JMP(parser.parse()?)),
            Ident::JSR => Ok(Self::JSR(parser.parse()?)),
            Ident::JSRR => Ok(Self::JSRR(parser.parse()?)),
            Ident::LD => {
                let dr = parser.parse()?;
                parser.match_(parse_comma)?;
                let off = parser.parse()?;

                Ok(Self::LD(dr, off))
            },
            Ident::LDI => {
                let dr = parser.parse()?;
                parser.match_(parse_comma)?;
                let off = parser.parse()?;

                Ok(Self::LDI(dr, off))
            },
            Ident::LDR => {
                let dr = parser.parse()?;
                parser.match_(parse_comma)?;
                let br = parser.parse()?;
                parser.match_(parse_comma)?;
                let off = parser.parse()?;

                Ok(Self::LDR(dr, br, off))
            },
            Ident::LEA => {
                let dr = parser.parse()?;
                parser.match_(parse_comma)?;
                let off = parser.parse()?;

                Ok(Self::LEA(dr, off))
            },
            Ident::ST => {
                let sr = parser.parse()?;
                parser.match_(parse_comma)?;
                let off = parser.parse()?;

                Ok(Self::ST(sr, off))
            },
            Ident::STI => {
                let sr = parser.parse()?;
                parser.match_(parse_comma)?;
                let off = parser.parse()?;

                Ok(Self::STI(sr, off))
            },
            Ident::STR => {
                let dr = parser.parse()?;
                parser.match_(parse_comma)?;
                let br = parser.parse()?;
                parser.match_(parse_comma)?;
                let off = parser.parse()?;

                Ok(Self::STR(dr, br, off))
            },
            Ident::TRAP => Ok(Self::TRAP(parser.parse()?)),
            Ident::NOP => Ok(Self::NOP),
            Ident::RET => Ok(Self::RET),
            Ident::RTI => Ok(Self::RTI),
            Ident::GETC => Ok(Self::GETC),
            Ident::OUT => Ok(Self::OUT),
            Ident::PUTC => Ok(Self::PUTC),
            Ident::PUTS => Ok(Self::PUTS),
            Ident::IN => Ok(Self::IN),
            Ident::PUTSP => Ok(Self::PUTSP),
            Ident::HALT => Ok(Self::HALT),
            Ident::Label(_) => Err(ParseErr::new("expected instruction")) // should be unreachable
        }
    }
}

impl Parse for Directive {
    fn parse(parser: &mut Parser<'_>) -> Result<Self, ParseErr> {
        let directive = parser.match_(|t| match t {
            Token::Unsigned(_)   => Err(ParseErr::new("unexpected numeric")),
            Token::Signed(_)     => Err(ParseErr::new("unexpected numeric")),
            Token::Reg(_)        => Err(ParseErr::new("unexpected register")),
            Token::Ident(_)      => Err(ParseErr::new("unexpected label")),
            Token::Directive(id) => Ok(id.to_string()),
            Token::String(_)     => Err(ParseErr::new("unexpected string literal")),
            Token::Colon         => Err(ParseErr::new("unexpected colon")),
            Token::Comma         => Err(ParseErr::new("unexpected comma")),
            Token::Comment       => Err(ParseErr::new("unexpected comment")), // FIXME
        })?;

        match &*directive.to_uppercase() {
            "ORIG" => Ok(Self::Orig(parser.parse()?)),
            "FILL" => {
                // Unlike other numeric operands, this can accept both unsigned or signed literals,
                // and therefore has to be handled differently.
                parser.match_(|t| {
                    let off_val = match *t {
                        Token::Unsigned(n) => Ok(n),
                        Token::Signed(n) => Ok(n as u16),
                        _ => Err(ParseErr::new("expected numeric"))
                    }?;
                    
                    let off = Offset::new(off_val)
                        .map_err(|s| ParseErr::new(s.to_string()))?;

                    Ok(Self::Fill(off))
                })
            }
            "BLKW" => {
                let block_size: Offset<_, 16> = parser.parse()?;
                match block_size.get() != 0 {
                    true  => Ok(Self::Blkw(block_size)),
                    false => Err(ParseErr::new("block size must be greater than 0"))
                }
            }
            "STRINGZ" => {
                let string = parser.match_(|t| match t {
                    Token::String(st) => Ok(st.to_string()),
                    _ => Err(ParseErr::new("expected string literal")),
                })?;

                Ok(Self::Stringz(string))
            }
            "END" => Ok(Self::End),
            _ => Err(ParseErr::new("invalid directive"))
        }
    }
}