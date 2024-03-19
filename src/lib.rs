//! A LC-3 parser, assembler, and simulator.
//! 
//! This is meant to be a general suite to use LC-3 assembly 
//! (meant as a backend for Georgia Tech's CS 2110 LC3Tools).

#![warn(missing_docs)]

pub mod parse;
pub mod ast;
pub mod asm;
pub mod sim;
pub mod err;
