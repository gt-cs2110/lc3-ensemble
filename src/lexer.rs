//! Lexer and parser of LC3 assembly.
//! This converts an LC3 assembly file into
//! an AST representation of each instruction.

use std::num::IntErrorKind;

use logos::{Lexer, Logos};

/// A unit of information in LC3 source code.
#[derive(Debug, Logos, PartialEq, Eq)]
#[logos(skip r"[ \t]+", error = LexErr)]
pub enum Token {
    /// A numeric value (e.g., `9`, `#9`, `0b1001`, `0x9`, `x9`, `b1001`, etc.)
    #[regex(r"\d+", parse_unsigned_dec)]
    #[regex(r"#\d+", parse_unsigned_dec)]
    #[regex(r"-\d+", parse_signed_dec)]
    #[regex(r"#-\d+", parse_signed_dec)]
    #[regex(r"0?[Xx][\dA-Fa-f]+", parse_hex)]
    #[regex(r"0?[Bb][01]+", parse_bin)]
    Numeric(u16),

    /// A register value (i.e., `R0`-`R7`)
    #[regex(r"[Rr][0-7]", parse_reg)]
    Reg(u8),

    /// An identifier. This can refer to either:
    /// - a label (e.g., `IF`, `WHILE`, `ENDIF`, `IF1`)
    /// - an instruction (e.g. `ADD`, `AND`, `NOT`)
    ///
    /// This token type is case insensitive. 
    /// It cannot be of the format X000, B000, or R000.
    #[regex(r"[A-Za-z_]\w*", |lx| lx.slice().to_string())]
    Ident(String),

    /// A directive (e.g. `.orig`, `.end`).
    #[regex(r"\.[A-Za-z_]\w*", |lx| lx.slice()[1..].to_string())]
    Directive(String),

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

/// Any errors raised in attempting to lex an input stream.
#[derive(Debug, PartialEq, Eq, Clone, Default)]
pub enum LexErr {
    /// Numeric literal (unsigned dec, hex, and bin) cannot fit within the range of a u16
    DoesNotFitU16,
    /// Numeric literal (signed dec) cannot fit within the range of a i16
    DoesNotFitI16,
    /// Hex literal (starting with 0x or x) has invalid hex digits (or there is nothing following)
    InvalidHex,
    /// Bin literal (starting with 0b or b) has invalid bin digits (or there is nothing following)
    InvalidBin,
    /// Numeric literal could not be parsed as an unsigned dec literal (typically because it's just `#`)
    InvalidUnsigned,
    /// Numeric literal could not be parsed as an signed dec literal (typically because it's just `#` or `#-` or `-`)
    InvalidSigned,
    /// Int parsing failed but the reason why is unknown
    UnknownIntErr,
    /// A symbol was used which is not allowed in LC3 assembly files
    #[default]
    InvalidSymbol
}

fn parse_unsigned_dec(lx: &Lexer<'_, Token>) -> Result<u16, LexErr> {
    let mut string = lx.slice();
    if lx.slice().starts_with('#') {
        string = &string[1..];
    }

    string.parse::<u16>()
        .map_err(|e| match e.kind() {
            IntErrorKind::Empty => LexErr::InvalidUnsigned,
            IntErrorKind::InvalidDigit => LexErr::InvalidUnsigned,
            IntErrorKind::PosOverflow => LexErr::DoesNotFitU16,
            IntErrorKind::NegOverflow => LexErr::DoesNotFitU16,
            IntErrorKind::Zero => unreachable!("IntErrorKind::Zero should not be emitted in parsing u16"),
            _ => LexErr::UnknownIntErr,
        })
}

fn parse_signed_dec(lx: &Lexer<'_, Token>) -> Result<u16, LexErr> {
    let mut string = lx.slice();
    if lx.slice().starts_with('#') {
        string = &string[1..];
    }

    match string.parse::<i16>() {
        Ok(val) => Ok(val as u16),
        Err(e) => {
            let kind = match e.kind() {
                IntErrorKind::Empty => LexErr::InvalidSigned,
                IntErrorKind::InvalidDigit => LexErr::InvalidSigned,
                IntErrorKind::PosOverflow => LexErr::DoesNotFitI16,
                IntErrorKind::NegOverflow => LexErr::DoesNotFitI16,
                IntErrorKind::Zero => unreachable!("IntErrorKind::Zero should not be emitted in parsing i16"),
                _ => LexErr::UnknownIntErr,
            };

            Err(kind)
        },
    }
}
fn parse_hex(lx: &Lexer<'_, Token>) -> Result<u16, LexErr> {
    let Some((_, hex)) = lx.slice().split_once(['X', 'x']) else {
        unreachable!("Lexer slice should have contained an X or x");
    };

    u16::from_str_radix(hex, 16)
        .map_err(|e| match e.kind() {
            IntErrorKind::Empty => LexErr::InvalidHex,
            IntErrorKind::InvalidDigit => LexErr::InvalidHex,
            IntErrorKind::PosOverflow => LexErr::DoesNotFitI16,
            IntErrorKind::NegOverflow => LexErr::DoesNotFitI16,
            IntErrorKind::Zero => unreachable!("IntErrorKind::Zero should not be emitted in parsing u16"),
            _ => LexErr::UnknownIntErr,
        })
}
fn parse_bin(lx: &Lexer<'_, Token>) -> Result<u16, LexErr> {
    let Some((_, bin)) = lx.slice().split_once(['B', 'b']) else {
        unreachable!("Lexer slice should have contained an B or b");
    };

    u16::from_str_radix(bin, 2)
        .map_err(|e| match e.kind() {
            IntErrorKind::Empty => LexErr::InvalidBin,
            IntErrorKind::InvalidDigit => LexErr::InvalidBin,
            IntErrorKind::PosOverflow => LexErr::DoesNotFitI16,
            IntErrorKind::NegOverflow => LexErr::DoesNotFitI16,
            IntErrorKind::Zero => unreachable!("IntErrorKind::Zero should not be emitted in parsing u16"),
            _ => LexErr::UnknownIntErr,
        })
}

fn parse_reg(lx: &Lexer<'_, Token>) -> u8 {
    let regno = lx.slice()[1..].parse()
        .unwrap_or_else(|_| unreachable!("parse_reg should only be called with register 0-7"));

    regno
}

#[cfg(test)]
mod test {
    use logos::Logos;

    use super::Token;

    #[test]
    fn fib() {
        let data = ";;=============================================================
        ;; CS 2110 - Spring 2024
        ;; Homework 5 - Fibonacci
        ;;=============================================================
        ;; Name: TA Solution
        ;;=============================================================
        
        
        ;; Suggested Pseudocode (see PDF for explanation)
        ;;
        ;; n = mem[N];
        ;; resAddr = mem[RESULT]
        ;; 
        ;; if (n == 1) {
        ;;     mem[resAddr] = 0;
        ;; } else if (n > 1) {
        ;;     mem[resAddr] = 0;
        ;;     mem[resAddr + 1] = 1;
        ;;     for (i = 2; i < n; i++) {
        ;;         x = mem[resAddr + i - 1];
        ;;         y = mem[resAddr + i - 2];
        ;;         mem[resAddr + i] = x + y;
        ;;     }
        ;; }
        
        .orig x3000
            
        LD R0, N     ;;R0 = n
        LD R7, RESULT ;;R7 = mem[RESULT] = result
        
        IF
            ;;check condition
            ADD R1, R0, -1   ;;n - 1
            BRnp ELIF
            AND R1, R1, 0    ;;R1 = 0
            STR R1, R7, 0    ;;mem[result] = 0
            BR END
        
        ELIF
            ;;check condition
            ADD R1, R0, -1   ;;n - 1
            BRnz END
            AND R1, R1, 0    ;;R1 = 0
            STR R1, R7, 0    ;;mem[result] = 0
            ADD R1, R1, 1    ;;R1 = 1
            STR R1, R7, 1    ;;mem[RESULT + 1] = 1
            ADD R1, R1, 1    ;;R1 = 2 = i    set up i for for loop
            FOR
                ;;check condition
                NOT R3, R0
                ADD R3, R3, 1    ;;R3 = -n          TIP: make sure students are not flipping n each time. I.e. n -> -n -> n
                ADD R3, R3, R1   ;;R3 = i - n
                BRzp END
        
                ADD R3, R7, R1   ;;R3 = result + i
                ADD R4, R3, -1   ;;R4 = result + i - 1
                ADD R5, R3, -2   ;;R5 = result + i - 2
        
                LDR R4, R4, 0    ;;R4 = x = mem[result + i - 1]
                LDR R5, R5, 0    ;;R5 = y = mem[result + i - 2]
        
                ADD R4, R4, R5   ;;x + y
                STR R4, R3, 0    ;;mem[result + i] = x + y
        
                ADD R1, R1, 1    ;;i++
                BR FOR
        
        
        END
        HALT
        
        ;; Do not rename or remove any existing labels
        ;; You may change the value of N for debugging
        N       .fill 5
        RESULT  .fill x4000
        .end
        
        .orig x4000
        .blkw 100
        .end";

        for line in data.lines() {
            println!("{:?}", Token::lexer(line).collect::<Vec<_>>());
        }
    }
    #[test]
    fn fib2() {
        let data = "
        .blkw 100000
        .blkw #2222 he
        .blkw x9999 he
        ";

        for line in data.lines() {
            println!("{:?}", Token::lexer(line).collect::<Vec<_>>());
        }
    }
}