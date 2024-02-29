//! Lexer and parser of LC3 assembly.
//! This converts an LC3 assembly file into
//! an AST representation of each instruction.

use logos::{Lexer, Logos};

/// A unit of information in LC3 source code.
#[derive(Debug, Logos)]
#[logos(skip r"[ \t]+")]
pub enum Token {
    /// A numeric value (e.g., `9`, `#9`, `0b1001`, `0x9`, `x9`, `b1001`, etc.)
    #[regex(r"-?\d+", |lx| lx.slice().parse::<i16>().unwrap())]
    #[regex(r"#-?\d+", |lx| lx.slice()[1..].parse::<i16>().unwrap())]
    #[regex(r"0?[Xx]\d+", parse_hex_literal)]
    #[regex(r"0?[Bb]\d+", parse_bin_literal)]
    Numeric(i16),

    /// A register value (i.e., `R0`-`R7`)
    #[regex(r"[Rr]\d+", parse_reg)]
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
    Comment,
}

fn parse_reg(lx: &Lexer<'_, Token>) -> u8 {
    let regno: u8 = lx.slice()[1..].parse().unwrap();
    
    if regno > 7 {
        panic!("LC3 does not support register number {regno}");
    }
    regno
}
fn parse_hex_literal(lx: &Lexer<'_, Token>) -> i16 {
    let Some((_, hex)) = lx.slice().split_once(['X', 'x']) else {
        unreachable!("Lexer slice should have contained an X or x");
    };

    i16::from_str_radix(hex, 16).unwrap()
}
fn parse_bin_literal(lx: &Lexer<'_, Token>) -> i16 {
    let Some((_, bin)) = lx.slice().split_once(['B', 'b']) else {
        unreachable!("Lexer slice should have contained an B or b");
    };

    i16::from_str_radix(bin, 2).unwrap()
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
}