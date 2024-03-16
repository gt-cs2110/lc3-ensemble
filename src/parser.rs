//! Parser that converts tokens from an LC-3 assembly file into
//! an AST.

use std::borrow::Cow;

use logos::Span;

use crate::ast::asm::{AsmInstr, Directive, Stmt, StmtKind};
use crate::ast::{ImmOrReg, Offset, PCOffset, Reg};
use crate::lexer::{Ident, Token};

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
        let Some((tok, _)) = self.peek() else { return Err(ParseErr::new("unexpected end of line")) };
        
        let result = pred(tok);
        if result.is_ok() {
            self.next();
        }
        result
    }
    fn match_end(&mut self) -> Result<(), ParseErr> {
        match self.peek() {
            Some(_) => Err(ParseErr::new("expected end of line")),
            None => Ok(())
        }
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
            Err(_) => match parser.match_(parse_label) {
                Ok(s) => Ok(PCOffset::Label(s)),
                Err(_) => Err(ParseErr::new("expected offset or label")),
            },
        }
    }
}

fn parse_comma(t: &Token) -> Result<(), ParseErr> {
    match t {
        Token::Comma => Ok(()),
        _ => Err(ParseErr::new("expected comma"))
    }
}
fn parse_colon(t: &Token) -> Result<(), ParseErr> {
    match t {
        Token::Colon => Ok(()),
        _ => Err(ParseErr::new("expected colon"))
    }
}
fn parse_label(t: &Token) -> Result<String, ParseErr> {
    match t {
        Token::Ident(Ident::Label(s)) => Ok(s.to_string()),
        _ => Err(ParseErr::new("expected offset or label"))
    }
}

impl Parse for AsmInstr {
    fn parse(parser: &mut Parser<'_>) -> Result<Self, ParseErr> {
        let opcode = parser.match_(|t| match t {
            Token::Ident(id) if !matches!(id, Ident::Label(_)) => Ok(id.clone()),
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
            Ident::NOT => {
                let dr = parser.parse()?;
                parser.match_(parse_comma)?;
                let sr = parser.parse()?;

                Ok(Self::NOT(dr, sr))
            },
            Ident::RET => Ok(Self::RET),
            Ident::RTI => Ok(Self::RTI),
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
                // .fill is weird.
                //
                // Unlike other numeric operands, it can accept both unsigned and signed literals,
                // so it cannot be parsed with PCOffset's parser, and therefore has to be handled differently.
                parser.match_(|t| {
                    let operand = 'operand: {
                        let off_val = match t {
                            &Token::Unsigned(n) => Ok(n),
                            &Token::Signed(n)   => Ok(n as u16),
                            Token::Ident(Ident::Label(s)) => break 'operand PCOffset::Label(s.to_string()),
                            _ => Err(ParseErr::new("expected numeric or label"))
                        }?;

                        let off = Offset::new(off_val)
                            .map_err(|s| ParseErr::new(s.to_string()))?;

                        PCOffset::Offset(off)
                    };
                    
                    Ok(Self::Fill(operand))
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

impl Parse for StmtKind {
    fn parse(parser: &mut Parser<'_>) -> Result<Self, ParseErr> {
        match parser.peek() {
            Some((Token::Directive(_), _)) => Ok(StmtKind::Directive(parser.parse()?)),
            Some((Token::Ident(id), _)) if !matches!(id, Ident::Label(_)) => Ok(StmtKind::Instr(parser.parse()?)),
            _ => Err(ParseErr::new("expected instruction or directive"))
        }
    }
}
impl Parse for Stmt {
    fn parse(parser: &mut Parser<'_>) -> Result<Self, ParseErr> {
        let mut labels = vec![];
        while let Ok(label) = parser.match_(parse_label) {
            let _ = parser.match_(parse_colon); // skip colon if it exists
            labels.push(label);
        }
        let nucleus = parser.parse()?;
        parser.match_end()?;

        Ok(Self { labels, nucleus })
    }
}