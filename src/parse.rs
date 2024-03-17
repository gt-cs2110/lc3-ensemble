//! Parsing assembly source code into an AST.
//! 
//! This module is used to convert strings (which represent assembly source code)
//! into abstract syntax trees that maintain all of the information of the source code
//! in an easier to handle format.
//! 
//! The parser module consists of:
//! - [`lex`]: the implementation of the lexer/tokenizer
//! - [`Parser`]: the main logic for the parser
//! - [`Parse`]: the implementation to "parse" an AST component

pub mod lex;

use std::borrow::Cow;

use logos::{Logos, Span};

use crate::ast::asm::{AsmInstr, Directive, Stmt, StmtKind};
use crate::ast::{IOffset, ImmOrReg, Offset, PCOffset};
use lex::{Ident, Token};
use simple::*;

/// Parses an assembly source code string into a `Vec` of statements.
/// 
/// This is a shortcut from repeatedly using the [`Parser`].
pub fn parse_ast(s: &str) -> Result<Vec<Stmt>, ParseErr> {
    let mut parser = Parser::new(s)?;
    // Horrendous one-liner version of this:
    // std::iter::from_fn(|| (!parser.is_empty()).then(|| parser.parse())).collect()
    std::iter::from_fn(|| match parser.is_empty() {
        true  => None,
        false => Some(parser.parse()),
    }).collect::<Result<Vec<_>, _>>()
}

/// Any error that occurs during parsing tokens.
#[derive(Debug)]
pub struct ParseErr {
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

/// Components that can be constructed from a sequence of tokens.
pub trait Parse: Sized {
    /// Attempt to convert the next sequence of tokens 
    /// in the parser's state into a component.
    /// 
    /// If parsing fails, there are no guarantees about what happens to the input,
    /// and the parser likely should not be used after an error is raised during parsing.
    fn parse(parser: &mut Parser) -> Result<Self, ParseErr>;
}

/// The main parser struct, which holds the main logic for the parser.
pub struct Parser {
    tokens: Vec<(Token, Span)>,
    index: usize
}
impl Parser {
    /// Creates a new parser from a given string.
    /// 
    /// In the instantiation process, 
    /// this function will attempt to tokenize the string into tokens,
    /// raising an error if it fails.
    pub fn new(stream: &str) -> Result<Self, ParseErr> {
        let tokens = Token::lexer(stream).spanned()
            .map(|(m_token, span)| match m_token {
                Ok(token) => Ok((token, span)),
                Err(err)  => Err(ParseErr::new(err.to_string(), span)),
            })
            .filter(|t| !matches!(t, Ok((Token::Comment, _)))) // filter comments
            .collect::<Result<_, _>>()?;

        Ok(Self { tokens, index: 0 })
    }

    /// Peeks at the next token to read.
    pub fn peek(&self) -> Option<&(Token, Span)> {
        self.tokens[self.index..].first()
    }
    /// Advances the parser ahead by one token.
    pub fn advance(&mut self) {
        self.index += 1;
        self.index = self.index.min(self.tokens.len());
    }
    /// Gets the range of the next token to read (or an EOL range if there are no more tokens to read).
    pub fn cursor(&self) -> Span {
        match self.peek().or_else(|| self.tokens.last()) {
            Some((_, span)) => span.clone(),
            None => 0..0
        }
    }

    /// Parses the current token stream into a component, erroring if not possible.
    /// 
    /// If parsing fails, there are no guarantees about what happens to the input,
    /// and the parser likely should not be used after an error is raised during parsing.
    pub fn parse<P: Parse>(&mut self) -> Result<P, ParseErr> {
        P::parse(self)
    }

    /// Consumes the next token if it represents the corresponding component.
    /// 
    /// This will not consume the next token if matching fails.
    pub fn match_<P: SimpleParse>(&mut self) -> Option<P> {
        // This is allowed because it's assured by SimpleParse's contract
        // that this does not consume input.
        self.parse().ok()
    }

    /// Applies the provided predicate to the next token in the input.
    /// 
    /// If an error is raised from the predicate, the parser does not advance its input.
    pub fn advance_if<T>(&mut self, pred: impl FnOnce(Option<&Token>, Span) -> Result<T, ParseErr>) -> Result<T, ParseErr> {
        let result = if let Some((tok, span)) = self.peek() {
            pred(Some(tok), span.clone())
        } else {
            pred(None, self.cursor())
        };
        if result.is_ok() {
            self.advance();
        }
        result
    }

    /// Checks whether the input for the parser is empty.
    pub fn is_empty(&self) -> bool {
        self.tokens[self.index..].is_empty()
    }
}

impl<const N: u32> Parse for ImmOrReg<N> {
    fn parse(parser: &mut Parser) -> Result<Self, ParseErr> {
        match parser.match_() {
            Some(Either::Left(imm))  => Ok(ImmOrReg::Imm(imm)),
            Some(Either::Right(reg)) => Ok(ImmOrReg::Reg(reg)),
            None => Err(ParseErr::new("expected register or immediate value", parser.cursor()))
        }
    }
}

impl<OFF, const N: u32> Parse for PCOffset<OFF, N> 
    where Offset<OFF, N>: SimpleParse
{
    fn parse(parser: &mut Parser) -> Result<Self, ParseErr> {
        match parser.match_() {
            Some(Either::Left(off)) => Ok(PCOffset::Offset(off)),
            Some(Either::Right(Label(s))) => Ok(PCOffset::Label(s)),
            None => Err(ParseErr::new("expected offset or label", parser.cursor()))
        }
    }
}

/// Simple to parse components.
/// 
/// This module holds components that are very simple to parse
/// (defined as only requiring a single token and no additional state from the parser).
/// 
/// The key type of this module is the [`SimpleParse`] module which defines
/// how to "simply parse" a component. 
/// See that trait for more details about its utility over [`Parse`].
/// 
/// This module also provides several utility parsers (e.g., [`Comma`] and [`Colon`])
/// for use in more complex component parsing.
pub mod simple {
    use logos::Span;

    use crate::ast::{Offset, Reg};

    use super::lex::{Ident, LexErr, Token};
    use super::{Parse, ParseErr, Parser};

    /// Components that can be constructed with a single token 
    /// and require no additional parser state.
    /// 
    /// This has an advantage over [`Parse`] in that if parsing fails,
    /// the parser is known to not advance its input. 
    /// This can be taken advantage of with [`Parser::match_`], 
    /// which only advances if parsing passes.
    /// 
    /// [`Parser::match_`]: super::Parser::match_
    pub trait SimpleParse: Sized {
        /// Tries to parse the provided token as a component, erroring if not possible.
        fn try_parse(m_token: Option<&Token>, span: Span) -> Result<Self, ParseErr>;
    }
    impl<S: SimpleParse> Parse for S {
        fn parse(parser: &mut Parser) -> Result<Self, ParseErr> {
            parser.advance_if(S::try_parse)
        }
    }

    /// Comma.
    #[derive(Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord, Debug, Default)]
    pub struct Comma;
    impl SimpleParse for Comma {
        fn try_parse(m_token: Option<&Token>, span: Span) -> Result<Self, ParseErr> {
            match m_token {
                Some(Token::Comma) => Ok(Comma),
                _ => Err(ParseErr::new("expected comma", span))
            }
        }
    }

    /// Colon.
    #[derive(Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord, Debug, Default)]
    pub struct Colon;
    impl SimpleParse for Colon {
        fn try_parse(m_token: Option<&Token>, span: Span) -> Result<Self, ParseErr> {
            match m_token {
                Some(Token::Colon) => Ok(Colon),
                _ => Err(ParseErr::new("expected comma", span))
            }
        }
    }

    /// A label.
    #[derive(Clone, PartialEq, Eq, Hash, PartialOrd, Ord, Debug, Default)]
    pub struct Label(pub String);
    impl SimpleParse for Label {
        fn try_parse(m_token: Option<&Token>, span: Span) -> Result<Self, ParseErr> {
            match m_token {
                Some(Token::Ident(Ident::Label(s))) => Ok(Label(s.to_string())),
                _ => Err(ParseErr::new("expected label", span))
            }
        }
    }

    /// A string literal.
    #[derive(Clone, PartialEq, Eq, Hash, PartialOrd, Ord, Debug, Default)]
    pub struct StrLiteral(pub String);
    impl SimpleParse for StrLiteral {
        fn try_parse(m_token: Option<&Token>, span: Span) -> Result<Self, ParseErr> {
            match m_token {
                Some(Token::String(s)) => Ok(StrLiteral(s.to_string())),
                _ => Err(ParseErr::new("expected string literal", span))
            }
        }
    }

    /// The end of a line or input.
    #[derive(Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord, Debug, Default)]
    pub struct End;
    impl SimpleParse for End {
        fn try_parse(m_token: Option<&Token>, span: Span) -> Result<Self, ParseErr> {
            match m_token {
                None | Some(Token::NewLine) => Ok(End),
                _ => Err(ParseErr::new("expected end of line", span))
            }
        }
    }

    /// Either one component or another.
    /// 
    /// This is not meant to be used as a general purpose Either type.
    /// It is only meant to be used for parsing.
    pub enum Either<L, R> {
        /// The first possible component.
        Left(L),
        /// The second possible component.
        Right(R)
    }
    impl<L: SimpleParse, R: SimpleParse> SimpleParse for Either<L, R> {
        fn try_parse(m_token: Option<&Token>, span: Span) -> Result<Self, ParseErr> {
            match L::try_parse(m_token, span.clone()) {
                Ok(t) => Ok(Either::Left(t)),
                Err(_) => match R::try_parse(m_token, span.clone()) {
                    Ok(u) => Ok(Either::Right(u)),
                    Err(_) => Err(ParseErr::new("could not parse", span)),
                },
            }
        }
    }

    impl SimpleParse for Reg {
        fn try_parse(m_token: Option<&Token>, span: Span) -> Result<Self, ParseErr> {
            match m_token {
                Some(&Token::Reg(reg)) => Ok(Reg(reg)),
                _ => Err(ParseErr::new("expected register", span))
            }
        }
    }

    impl<const N: u32> SimpleParse for Offset<i16, N> {
        fn try_parse(m_token: Option<&Token>, span: Span) -> Result<Self, ParseErr> {
            let off_val = match m_token {
                Some(&Token::Unsigned(n)) => {
                    i16::try_from(n)
                        .map_err(|_| ParseErr::new(LexErr::DoesNotFitI16.to_string(), span.clone()))
                },
                Some(&Token::Signed(n)) => Ok(n),
                _ => Err(ParseErr::new("expected immediate value", span.clone()))
            }?;
            
            Self::new(off_val)
                .map_err(|s| ParseErr::new(s.to_string(), span))
        }
    }

    impl<const N: u32> SimpleParse for Offset<u16, N> {
        fn try_parse(m_token: Option<&Token>, span: Span) -> Result<Self, ParseErr> {
            let off_val = match m_token {
                Some(&Token::Unsigned(n)) => Ok(n),
                Some(&Token::Signed(n)) => {
                    u16::try_from(n)
                        .map_err(|_| ParseErr::new(LexErr::DoesNotFitU16.to_string(), span.clone()))
                },
                _ => Err(ParseErr::new("expected immediate value", span.clone()))
            }?;
            
            Self::new(off_val)
                .map_err(|s| ParseErr::new(s.to_string(), span))
        }
    }
}

impl Parse for AsmInstr {
    fn parse(parser: &mut Parser) -> Result<Self, ParseErr> {
        let opcode = parser.advance_if(|mt, span| match mt {
            Some(Token::Ident(id)) if !matches!(id, Ident::Label(_)) => Ok(id.clone()),
            _ => Err(ParseErr::new("expected instruction", span))
        })?;

        match opcode {
            Ident::ADD => {
                let dr = parser.parse()?;
                parser.parse::<Comma>()?;
                let sr1 = parser.parse()?;
                parser.parse::<Comma>()?;
                let sr2 = parser.parse()?;

                Ok(Self::ADD(dr, sr1, sr2))
            },
            Ident::AND => {
                let dr = parser.parse()?;
                parser.parse::<Comma>()?;
                let sr1 = parser.parse()?;
                parser.parse::<Comma>()?;
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
                parser.parse::<Comma>()?;
                let off = parser.parse()?;

                Ok(Self::LD(dr, off))
            },
            Ident::LDI => {
                let dr = parser.parse()?;
                parser.parse::<Comma>()?;
                let off = parser.parse()?;

                Ok(Self::LDI(dr, off))
            },
            Ident::LDR => {
                let dr = parser.parse()?;
                parser.parse::<Comma>()?;
                let br = parser.parse()?;
                parser.parse::<Comma>()?;
                let off = parser.parse()?;

                Ok(Self::LDR(dr, br, off))
            },
            Ident::LEA => {
                let dr = parser.parse()?;
                parser.parse::<Comma>()?;
                let off = parser.parse()?;

                Ok(Self::LEA(dr, off))
            },
            Ident::NOT => {
                let dr = parser.parse()?;
                parser.parse::<Comma>()?;
                let sr = parser.parse()?;

                Ok(Self::NOT(dr, sr))
            },
            Ident::RET => Ok(Self::RET),
            Ident::RTI => Ok(Self::RTI),
            Ident::ST => {
                let sr = parser.parse()?;
                parser.parse::<Comma>()?;
                let off = parser.parse()?;

                Ok(Self::ST(sr, off))
            },
            Ident::STI => {
                let sr = parser.parse()?;
                parser.parse::<Comma>()?;
                let off = parser.parse()?;

                Ok(Self::STI(sr, off))
            },
            Ident::STR => {
                let dr = parser.parse()?;
                parser.parse::<Comma>()?;
                let br = parser.parse()?;
                parser.parse::<Comma>()?;
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
        use Either::*;

        let directive = parser.advance_if(|mt, span| match mt {
            Some(Token::Directive(id)) => Ok(id.to_string()),
            _ => Err(ParseErr::new("expected directive", span))
        })?;

        match &*directive.to_uppercase() {
            "ORIG" => Ok(Self::Orig(parser.parse()?)),
            "FILL" => {
                // .fill is weird.
                //
                // Unlike other numeric operands, it can accept both unsigned and signed literals,
                // so it cannot be parsed with PCOffset's parser and has to be handled differently.
                let operand = match parser.match_::<Either<Label, Either<Offset<u16, 16>, IOffset<16>>>>() {
                    Some(Left(Label(s)))    => Ok(PCOffset::Label(s)),
                    Some(Right(Left(off)))  => Ok(PCOffset::Offset(off)),
                    Some(Right(Right(off))) => Ok(PCOffset::Offset(Offset::new_trunc(off.get() as u16))),
                    _ => Err(ParseErr::new("expected numeric or label", parser.cursor()))
                }?;

                Ok(Self::Fill(operand))
            }
            "BLKW" => {
                let block_size: Offset<_, 16> = parser.parse()?;
                match block_size.get() != 0 {
                    true  => Ok(Self::Blkw(block_size)),
                    false => Err(ParseErr::new("block size must be greater than 0", parser.cursor()))
                }
            }
            "STRINGZ" => {
                let StrLiteral(s) = parser.parse()?;
                Ok(Self::Stringz(s))
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

        // Scan through labels and new lines until we find an instruction
        while !parser.is_empty() {
            match parser.match_() {
                Some(Either::Left(Label(label))) => {
                    parser.match_::<Colon>(); // skip colon if it exists
                    labels.push(label);
                }
                Some(Either::Right(End)) => {},
                _ => break
            }
        }
        
        let nucleus = parser.parse()?;
        parser.parse::<End>()?;

        Ok(Self { labels, nucleus })
    }
}