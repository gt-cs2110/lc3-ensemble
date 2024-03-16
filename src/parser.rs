use std::borrow::Cow;

use logos::Span;

use crate::ast::{CondCode, IOffset, ImmOrReg, Offset, PCOffset, Reg, TrapVect8};
use crate::lexer::{Ident, Token};

type PCOffset9 = PCOffset<i16, 9>;
type PCOffset11 = PCOffset<i16, 11>;

enum Instruction {
    Add(Reg, Reg, ImmOrReg<5>),
    And(Reg, Reg, ImmOrReg<5>),
    Not(Reg, Reg),
    Br(CondCode, PCOffset9),
    Jmp(Reg),
    Jsr(PCOffset11),
    Jsrr(Reg),
    Ld(Reg, PCOffset9),
    Ldi(Reg, PCOffset9),
    Ldr(Reg, Reg, IOffset<6>),
    Lea(Reg, PCOffset9),
    St(Reg, PCOffset9),
    Sti(Reg, PCOffset9),
    Str(Reg, Reg, IOffset<6>),
    Trap(TrapVect8),

    // Extra instructions
    Nop,
    Ret,
    Rti,
    Getc,
    Out,
    Putc,
    Puts,
    In,
    Putsp,
    Halt
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
            Instruction::Lea(dr, off) => write!(f, "LEA {dr}, {off}"),
            Instruction::St(sr, off) => write!(f, "ST {sr}, {off}"),
            Instruction::Sti(sr, off) => write!(f, "STI {sr}, {off}"),
            Instruction::Str(sr, br, off) => write!(f, "STR {sr}, {br}, {off}"),
            Instruction::Trap(vect) => write!(f, "TRAP {vect:02X}"),
            Instruction::Nop   => f.write_str("NOP"),
            Instruction::Ret   => f.write_str("RET"),
            Instruction::Rti   => f.write_str("RTI"),
            Instruction::Getc  => f.write_str("GETC"),
            Instruction::Out   => f.write_str("OUT"),
            Instruction::Putc  => f.write_str("PUTC"),
            Instruction::Puts  => f.write_str("PUTS"),
            Instruction::In    => f.write_str("IN"),
            Instruction::Putsp => f.write_str("PUTSP"),
            Instruction::Halt  => f.write_str("HALT"),
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

                Ok(Self::Add(dr, sr1, sr2))
            },
            Ident::AND => {
                let dr = parser.parse()?;
                parser.match_(parse_comma)?;
                let sr1 = parser.parse()?;
                parser.match_(parse_comma)?;
                let sr2 = parser.parse()?;

                Ok(Self::And(dr, sr1, sr2))
            },
            Ident::NOT => {
                let dr = parser.parse()?;
                parser.match_(parse_comma)?;
                let sr = parser.parse()?;

                Ok(Self::Not(dr, sr))
            },
            Ident::BR => Ok(Self::Br(0b111, parser.parse()?)),
            Ident::BRP => Ok(Self::Br(0b001, parser.parse()?)),
            Ident::BRZ => Ok(Self::Br(0b010, parser.parse()?)),
            Ident::BRZP => Ok(Self::Br(0b011, parser.parse()?)),
            Ident::BRN => Ok(Self::Br(0b100, parser.parse()?)),
            Ident::BRNP => Ok(Self::Br(0b101, parser.parse()?)),
            Ident::BRNZ => Ok(Self::Br(0b110, parser.parse()?)),
            Ident::BRNZP => Ok(Self::Br(0b111, parser.parse()?)),
            Ident::JMP => Ok(Self::Jmp(parser.parse()?)),
            Ident::JSR => Ok(Self::Jsr(parser.parse()?)),
            Ident::JSRR => Ok(Self::Jsrr(parser.parse()?)),
            Ident::LD => {
                let dr = parser.parse()?;
                parser.match_(parse_comma)?;
                let off = parser.parse()?;

                Ok(Self::Ld(dr, off))
            },
            Ident::LDI => {
                let dr = parser.parse()?;
                parser.match_(parse_comma)?;
                let off = parser.parse()?;

                Ok(Self::Ldi(dr, off))
            },
            Ident::LDR => {
                let dr = parser.parse()?;
                parser.match_(parse_comma)?;
                let br = parser.parse()?;
                parser.match_(parse_comma)?;
                let off = parser.parse()?;

                Ok(Self::Ldr(dr, br, off))
            },
            Ident::LEA => {
                let dr = parser.parse()?;
                parser.match_(parse_comma)?;
                let off = parser.parse()?;

                Ok(Self::Lea(dr, off))
            },
            Ident::ST => {
                let sr = parser.parse()?;
                parser.match_(parse_comma)?;
                let off = parser.parse()?;

                Ok(Self::St(sr, off))
            },
            Ident::STI => {
                let sr = parser.parse()?;
                parser.match_(parse_comma)?;
                let off = parser.parse()?;

                Ok(Self::Sti(sr, off))
            },
            Ident::STR => {
                let dr = parser.parse()?;
                parser.match_(parse_comma)?;
                let br = parser.parse()?;
                parser.match_(parse_comma)?;
                let off = parser.parse()?;

                Ok(Self::Str(dr, br, off))
            },
            Ident::TRAP => Ok(Self::Trap(parser.parse()?)),
            Ident::NOP => Ok(Self::Nop),
            Ident::RET => Ok(Self::Ret),
            Ident::RTI => Ok(Self::Rti),
            Ident::GETC => Ok(Self::Getc),
            Ident::OUT => Ok(Self::Out),
            Ident::PUTC => Ok(Self::Putc),
            Ident::PUTS => Ok(Self::Puts),
            Ident::IN => Ok(Self::In),
            Ident::PUTSP => Ok(Self::Putsp),
            Ident::HALT => Ok(Self::Halt),
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