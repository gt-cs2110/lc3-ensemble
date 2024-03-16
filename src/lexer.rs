//! Tokenizer for LC-3 assembly.
//! 
//! This converts an LC-3 assembly file
//! into a set of tokens, which can be
//! converted to an AST by the [`parser`] module.
//! 
//! [`parser`]: crate::parser

use std::num::IntErrorKind;

use logos::{Lexer, Logos};

/// A unit of information in LC3 source code.
#[derive(Debug, Logos, PartialEq, Eq)]
#[logos(skip r"[ \t]+", error = LexErr)]
pub enum Token {
    /// An unsigned numeric value (e.g., `9`, `#14`, x7F`, etc.)
    #[regex(r"\d+", parse_unsigned_dec)]
    #[regex(r"#\d+", parse_unsigned_dec)]
    #[regex(r"[Xx][\dA-Fa-f]+", parse_unsigned_hex)]
    Unsigned(u16),

    /// A signed numeric value (e.g., `-9`, `#-14`, x-7F`, etc.)
    #[regex(r"-\d+", parse_signed_dec)]
    #[regex(r"#-\d+", parse_signed_dec)]
    #[regex(r"[Xx]-[\dA-Fa-f]+", parse_signed_hex)]
    Signed(i16),

    /// A register value (i.e., `R0`-`R7`)
    #[regex(r"[Rr][0-7]", parse_reg)]
    Reg(u8),

    /// An identifier. This can refer to either:
    /// - a label (e.g., `IF`, `WHILE`, `ENDIF`, `IF1`)
    /// - an instruction (e.g. `ADD`, `AND`, `NOT`)
    ///
    /// This token type is case insensitive. 
    #[regex(r"[A-Za-z_]\w*", |lx| lx.slice().parse::<Ident>().expect("should be infallible"))]
    Ident(Ident),

    /// A directive (e.g., `.orig`, `.end`).
    #[regex(r"\.[A-Za-z_]\w*", |lx| lx.slice()[1..].to_string())]
    Directive(String),

    /// A string literal (e.g., `"Hello!`)
    #[regex(r#"".+[^\\]""#, parse_str_literal)]
    String(String),

    /// A colon, which can optionally appear after labels
    #[token(":")]
    Colon,

    /// A comma, which delineate operands of an instruction
    #[token(",")]
    Comma,

    /// A comment, which starts with a semicolon and spans the remaining part of the line.
    #[regex(r";.*")]
    Comment
}

macro_rules! ident_enum {
    ($($instr:ident),+) => {
        /// An identifier. This can refer to either:
        /// - a label (e.g., `IF`, `WHILE`, `ENDIF`, `IF1`)
        /// - an instruction (e.g. `ADD`, `AND`, `NOT`)
        ///
        /// This token type is case insensitive. 
        #[derive(Debug, PartialEq, Eq, Clone)]
        pub enum Ident {
            $(
                #[allow(missing_docs)]
                $instr
            ),+,
            #[allow(missing_docs)]
            Label(String)
        }

        impl std::str::FromStr for Ident {
            type Err = std::convert::Infallible;
        
            fn from_str(s: &str) -> Result<Self, Self::Err> {
                match s {
                    $(stringify!($instr) => Ok(Self::$instr)),*,
                    s => Ok(Self::Label(s.to_string()))
                }
            }
        }

        impl std::fmt::Display for Ident {
            fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                match self {
                    $(Self::$instr => f.write_str(stringify!($instr))),*,
                    Self::Label(id) => f.write_str(id)
                }
            }
        }
    };
}
ident_enum! {
    ADD, AND, NOT, BR, BRP, BRZ, BRZP, BRN, BRNP, BRNZ, BRNZP, 
    JMP, JSR, JSRR, LD, LDI, LDR, LEA, ST, STI, STR, TRAP, NOP, 
    RET, RTI, GETC, OUT, PUTC, PUTS, IN, PUTSP, HALT
}

/// Any errors raised in attempting to lex an input stream.
#[derive(Debug, PartialEq, Eq, Clone, Copy, Default)]
pub enum LexErr {
    /// Numeric literal (unsigned dec, hex, and bin) cannot fit within the range of a u16
    DoesNotFitU16,
    /// Numeric literal (signed dec) cannot fit within the range of a i16
    DoesNotFitI16,
    /// Hex literal (starting with 0x or x) has invalid hex digits (or there is nothing following)
    InvalidHex,
    /// Bin literal (starting with 0b or b) has invalid bin digits (or there is nothing following)
    InvalidBin,
    /// Numeric literal could not be parsed as a decimal literal (typically because it's just `#` or `#-` or `-`)
    InvalidNumeric,
    /// Int parsing failed but the reason why is unknown
    UnknownIntErr,
    /// A symbol was used which is not allowed in LC3 assembly files
    #[default]
    InvalidSymbol
}

/// Helper that converts an int error kind to its corresponding LexErr, based on the provided inputs.
fn convert_int_error(e: &std::num::IntErrorKind, invalid_fmt_err: LexErr, overflow_err: LexErr) -> LexErr {
    match e {
        IntErrorKind::Empty        => invalid_fmt_err,
        IntErrorKind::InvalidDigit => invalid_fmt_err,
        IntErrorKind::PosOverflow  => overflow_err,
        IntErrorKind::NegOverflow  => overflow_err,
        IntErrorKind::Zero         => unreachable!("IntErrorKind::Zero should not be emitted in parsing u16"),
        _ => LexErr::UnknownIntErr,
    }
}
fn parse_unsigned_dec(lx: &Lexer<'_, Token>) -> Result<u16, LexErr> {
    let mut string = lx.slice();
    if lx.slice().starts_with('#') {
        string = &string[1..];
    }

    string.parse::<u16>()
        .map_err(|e| convert_int_error(e.kind(), LexErr::InvalidNumeric, LexErr::DoesNotFitU16))
}

fn parse_signed_dec(lx: &Lexer<'_, Token>) -> Result<i16, LexErr> {
    let mut string = lx.slice();
    if lx.slice().starts_with('#') {
        string = &string[1..];
    }

    string.parse::<i16>()
        .map_err(|e| convert_int_error(e.kind(), LexErr::InvalidNumeric, LexErr::DoesNotFitI16))
}
fn parse_unsigned_hex(lx: &Lexer<'_, Token>) -> Result<u16, LexErr> {
    let Some(hex) = lx.slice().strip_prefix(['X', 'x']) else {
        unreachable!("Lexer slice should have contained an X or x");
    };

    u16::from_str_radix(hex, 16)
        .map_err(|e| convert_int_error(e.kind(), LexErr::InvalidNumeric, LexErr::DoesNotFitU16))
}
fn parse_signed_hex(lx: &Lexer<'_, Token>) -> Result<i16, LexErr> {
    let Some(hex) = lx.slice().strip_prefix(['X', 'x']) else {
        unreachable!("Lexer slice should have contained an X or x");
    };

    i16::from_str_radix(hex, 16)
        .map_err(|e| convert_int_error(e.kind(), LexErr::InvalidNumeric, LexErr::DoesNotFitI16))
}
fn parse_reg(lx: &Lexer<'_, Token>) -> u8 {
    let regno = lx.slice()[1..].parse()
        .unwrap_or_else(|_| unreachable!("parse_reg should only be called with register 0-7"));

    regno
}
fn parse_str_literal(lx: &Lexer<'_, Token>) -> String {
    // get the string inside quotes:
    let mut remaining = &lx.slice()[1..(lx.slice().len() - 1)];
    let mut buf = String::with_capacity(remaining.len());

    // Look for escapes. Only a simple group of escapes are implemented.
    // (e.g., `\n`, `\r`, etc.)
    while let Some((left, right)) = remaining.split_once('\\') {
        buf.push_str(left);

        // this character is part of the escape:
        let esc = right.as_bytes()
            .first()
            .unwrap_or_else(|| unreachable!("expected character after escape")); // there always has to be one, cause last character is not \
        match esc {
            b'n'  => buf.push('\n'),
            b'r'  => buf.push('\r'),
            b't'  => buf.push('\t'),
            b'\\' => buf.push('\\'),
            b'0'  => buf.push('\0'),
            b'"'  => buf.push('\"'),
            &c => {
                buf.push('\\');
                buf.push(char::from(c));
            }
        }
        
        remaining = &right[1..];
    }
    buf.push_str(remaining);
    buf
}