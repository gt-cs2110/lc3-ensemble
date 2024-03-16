//! Parser that converts tokens from an LC-3 assembly file into
//! an AST.

use std::borrow::Cow;

use logos::{Logos, Span};

use crate::ast::asm::{AsmInstr, Directive, Stmt, StmtKind};
use crate::ast::{ImmOrReg, Offset, PCOffset, Reg};
use crate::lexer::{Ident, Token};

#[derive(Debug)]
struct ParseErr {
    msg: Cow<'static, str>,
    span: Span
}
impl ParseErr {
    fn new<C: Into<Cow<'static, str>>>(msg: C, span: Span) -> Self {
        Self { msg: msg.into(), span }
    }
}
impl std::fmt::Display for ParseErr {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{:?}: {}", self.span, self.msg)
    }
}

trait Parse: Sized {
    fn parse(parser: &mut Parser) -> Result<Self, ParseErr>;
}

struct Parser {
    tokens: Vec<(Token, Span)>,
    index: usize
}
impl Parser {
    fn new(stream: &str) -> Result<Self, ParseErr> {
        let tokens = Token::lexer(stream).spanned()
            .map(|(m_token, span)| match m_token {
                Ok(token) => Ok((token, span)),
                Err(err)  => Err(ParseErr::new(err.to_string(), span)),
            })
            .filter(|t| !matches!(t, Ok((Token::Comment, _)))) // filter comments
            .collect::<Result<_, _>>()?;

        Ok(Self { tokens, index: 0 })
    }

    fn peek(&self) -> Option<&(Token, Span)> {
        self.tokens[self.index..].first()
    }
    fn advance(&mut self) {
        self.index += 1;
        self.index = self.index.min(self.tokens.len());
    }
    fn cursor(&self) -> Span {
        match self.peek().or_else(|| self.tokens.last()) {
            Some((_, span)) => span.clone(),
            None => 0..0
        }
    }

    fn parse<P: Parse>(&mut self) -> Result<P, ParseErr> {
        P::parse(self)
    }
    fn match_<T>(&mut self, pred: impl FnOnce(&Token, Span) -> Result<T, ParseErr>) -> Result<T, ParseErr> {
        let Some((tok, span)) = self.peek() else { return Err(ParseErr::new("unexpected end of line", self.cursor())) };
        
        let result = pred(tok, span.clone());
        if result.is_ok() {
            self.advance();
        }
        result
    }
    fn match_nl(&mut self) -> Result<(), ParseErr> {
        match self.peek() {
            Some((Token::NewLine, _)) | None => {
                self.advance();
                Ok(())
            }
            Some(_) => Err(ParseErr::new("expected end of line", self.cursor())),
        }
    }
}

impl Parse for Reg {
    fn parse(parser: &mut Parser) -> Result<Self, ParseErr> {
        parser.match_(|t, span| match t {
            &Token::Reg(reg) => Ok(Reg(reg)),
            _ => Err(ParseErr::new("expected register", span)),
        })
    }
}
impl<const N: u32> Parse for ImmOrReg<N> {
    fn parse(parser: &mut Parser) -> Result<Self, ParseErr> {
        match parser.parse() {
            Ok(imm) => Ok(ImmOrReg::Imm(imm)),
            Err(_) => match parser.parse() {
                Ok(reg) => Ok(ImmOrReg::Reg(reg)),
                Err(_) => Err(ParseErr::new("expected immediate value or register", parser.cursor())),
            }
        }
    }
}

impl<const N: u32> Parse for Offset<i16, N> {
    fn parse(parser: &mut Parser) -> Result<Self, ParseErr> {
        parser.match_(|t, span| {
            let off_val = match *t {
                Token::Unsigned(n) => i16::try_from(n).map_err(|_| todo!("impl lex error if overflow")),
                Token::Signed(n) => Ok(n),
                _ => Err(ParseErr::new("expected immediate value", span.clone()))
            }?;
            
            Self::new(off_val)
                .map_err(|s| ParseErr::new(s.to_string(), span))
        })
    }
}
impl<const N: u32> Parse for Offset<u16, N> {
    fn parse(parser: &mut Parser) -> Result<Self, ParseErr> {
        parser.match_(|t, span| {
            let off_val = match *t {
                Token::Unsigned(n) => Ok(n),
                Token::Signed(n) => u16::try_from(n).map_err(|_| todo!("impl lex error if overflow")),
                _ => Err(ParseErr::new("expected immediate value", span.clone()))
            }?;
            
            Self::new(off_val)
                .map_err(|s| ParseErr::new(s.to_string(), span))
        })
    }
}

impl<OFF, const N: u32> Parse for PCOffset<OFF, N> 
    where Offset<OFF, N>: Parse
{
    fn parse(parser: &mut Parser) -> Result<Self, ParseErr> {
        match parser.parse() {
            Ok(off) => Ok(PCOffset::Offset(off)),
            Err(_) => match parser.match_(parse_label) {
                Ok(s) => Ok(PCOffset::Label(s)),
                Err(_) => Err(ParseErr::new("expected offset or label", parser.cursor())),
            },
        }
    }
}

fn parse_comma(t: &Token, span: Span) -> Result<(), ParseErr> {
    match t {
        Token::Comma => Ok(()),
        _ => Err(ParseErr::new("expected comma", span))
    }
}
fn parse_colon(t: &Token, span: Span) -> Result<(), ParseErr> {
    match t {
        Token::Colon => Ok(()),
        _ => Err(ParseErr::new("expected colon", span))
    }
}
fn parse_label(t: &Token, span: Span) -> Result<String, ParseErr> {
    match t {
        Token::Ident(Ident::Label(s)) => Ok(s.to_string()),
        _ => Err(ParseErr::new("expected offset or label", span))
    }
}

impl Parse for AsmInstr {
    fn parse(parser: &mut Parser) -> Result<Self, ParseErr> {
        let opcode = parser.match_(|t, span| match t {
            Token::Ident(id) if !matches!(id, Ident::Label(_)) => Ok(id.clone()),
            _ => Err(ParseErr::new("expected instruction", span))
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
            Ident::Label(_) => Err(ParseErr::new("expected instruction", parser.cursor())) // should be unreachable
        }
    }
}

impl Parse for Directive {
    fn parse(parser: &mut Parser) -> Result<Self, ParseErr> {
        let directive = parser.match_(|t, span| match t {
            Token::Unsigned(_)   => Err(ParseErr::new("unexpected numeric", span)),
            Token::Signed(_)     => Err(ParseErr::new("unexpected numeric", span)),
            Token::Reg(_)        => Err(ParseErr::new("unexpected register", span)),
            Token::Ident(_)      => Err(ParseErr::new("unexpected label", span)),
            Token::Directive(id) => Ok(id.to_string()),
            Token::String(_)     => Err(ParseErr::new("unexpected string literal", span)),
            Token::Colon         => Err(ParseErr::new("unexpected colon", span)),
            Token::Comma         => Err(ParseErr::new("unexpected comma", span)),
            Token::Comment       => Err(ParseErr::new("unexpected comment", span)),
            Token::NewLine       => Err(ParseErr::new("unexpected new line", span)),
        })?;

        match &*directive.to_uppercase() {
            "ORIG" => Ok(Self::Orig(parser.parse()?)),
            "FILL" => {
                // .fill is weird.
                //
                // Unlike other numeric operands, it can accept both unsigned and signed literals,
                // so it cannot be parsed with PCOffset's parser, and therefore has to be handled differently.
                parser.match_(|t, span| {
                    let operand = 'operand: {
                        let off_val = match t {
                            &Token::Unsigned(n) => Ok(n),
                            &Token::Signed(n)   => Ok(n as u16),
                            Token::Ident(Ident::Label(s)) => break 'operand PCOffset::Label(s.to_string()),
                            _ => Err(ParseErr::new("expected numeric or label", span.clone()))
                        }?;

                        let off = Offset::new(off_val)
                            .map_err(|s| ParseErr::new(s.to_string(), span))?;

                        PCOffset::Offset(off)
                    };
                    
                    Ok(Self::Fill(operand))
                })
            }
            "BLKW" => {
                let block_size: Offset<_, 16> = parser.parse()?;
                match block_size.get() != 0 {
                    true  => Ok(Self::Blkw(block_size)),
                    false => Err(ParseErr::new("block size must be greater than 0", parser.cursor()))
                }
            }
            "STRINGZ" => {
                let string = parser.match_(|t, span| match t {
                    Token::String(st) => Ok(st.to_string()),
                    _ => Err(ParseErr::new("expected string literal", span)),
                })?;

                Ok(Self::Stringz(string))
            }
            "END" => Ok(Self::End),
            _ => Err(ParseErr::new("invalid directive", parser.cursor()))
        }
    }
}

impl Parse for StmtKind {
    fn parse(parser: &mut Parser) -> Result<Self, ParseErr> {
        match parser.peek() {
            Some((Token::Directive(_), _)) => Ok(StmtKind::Directive(parser.parse()?)),
            Some((Token::Ident(id), _)) if !matches!(id, Ident::Label(_)) => Ok(StmtKind::Instr(parser.parse()?)),
            _ => Err(ParseErr::new("expected instruction or directive", parser.cursor()))
        }
    }
}
impl Parse for Stmt {
    fn parse(parser: &mut Parser) -> Result<Self, ParseErr> {
        let mut labels = vec![];
        while let Ok(label) = parser.match_(parse_label) {
            let _ = parser.match_(parse_colon); // skip colon if it exists
            let _ = parser.match_nl(); // skip new line if it exists
            labels.push(label);
        }
        let nucleus = parser.parse()?;
        parser.match_nl()?;

        Ok(Self { labels, nucleus })
    }
}