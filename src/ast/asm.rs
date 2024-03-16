//! This module is used for holding simulation instructions ([`Self`]),
//! which are instructions that directly map to assembly code.
//! 
//! For instructions that map bytecode, see [`sim::SimInstr`].
//! 
//! [`sim::SimInstr`]: [`crate::ast::sim::SimInstr`]

use std::fmt::Write as _;

use super::{CondCode, IOffset, ImmOrReg, Offset, PCOffset, Reg, TrapVect8};


type PCOffset9 = PCOffset<i16, 9>;
type PCOffset11 = PCOffset<i16, 11>;

/// An enum representing all of the possible instructions in LC-3 assembly code.
/// 
/// The variants in this enum represent instructions before assembly passes.
/// 
/// For instructions that map to typeable assembly code, refer to [`sim::SimInstr`].
/// 
/// [`sim::SimInstr`]: [`crate::ast::sim::SimInstr`]
pub enum AsmInstr {
    /// An ADD instruction.
    /// 
    /// # Operation
    /// 
    /// Evaluates the two operands, adds them, and stores the result to the destination register (`DR`).
    /// This also sets the condition code for the LC-3 machine.
    /// 
    /// # Syntax
    /// - `ADD DR, SR1, SR2`
    /// - `ADD DR, SR1, imm5`
    ADD(Reg, Reg, ImmOrReg<5>),

    /// An AND instruction.
    /// 
    /// # Operation
    /// 
    /// Evaluates the two operands, bitwise ANDs them, and stores the result to the destination register (`DR`).
    /// This also sets the condition code for the LC-3 machine.
    /// 
    /// # Syntax
    /// - `AND DR, SR1, SR2`
    /// - `AND DR, SR1, imm5`
    AND(Reg, Reg, ImmOrReg<5>),

    /// A BR instruction.
    /// 
    /// # Operation
    /// 
    /// Checks the current condition code and branches to the given `PCOffset9` 
    /// if the condition code matches one of the provided condition codes of the instruction.
    /// 
    /// # Syntax
    /// - `BR PCOffset9` (equivalent to `BRnzp`),
    /// - `BRn PCOffset9`
    /// - `BRz PCOffset9`
    /// - `BRnz PCOffset9`
    /// - `BRp PCOffset9`
    /// - `BRnp PCOffset9`
    /// - `BRzp PCOffset9`
    /// - `BRnzp PCOffset9`
    BR(CondCode, PCOffset9),
    
    /// A JMP instruction.
    /// 
    /// # Operation
    /// 
    /// Unconditionally jumps to the location stored in the given register (`BR`).
    /// 
    /// # Syntax
    /// - `JMP BR`
    JMP(Reg),
    
    /// A JSR instruction.
    /// 
    /// # Operation
    /// 
    /// Jumps to a given subroutine. This is done by storing the current PC into R7,
    /// and then unconditionally jumping to the location of the given `PCOffset11`.
    /// 
    /// # Syntax
    /// - `JSR PCOffset11`
    JSR(PCOffset11),
    
    /// A JSRR instruction.
    /// 
    /// # Operation
    /// 
    /// Jumps to a given subroutine. This is done by storing the current PC into R7,
    /// and then unconditionally jumping to the location stored in the given register (`BR`).
    /// 
    /// # Syntax
    /// - `JSR BR`
    JSRR(Reg),
    
    /// A LD instruction.
    /// 
    /// # Operation
    /// 
    /// Computes an effective address (`PC + PCOffset9`), accesses the memory at that address,
    /// and stores it to the destination register (`DR`).
    /// This also sets the condition code for the LC-3 machine.
    /// 
    /// # Syntax
    /// - `LD DR, PCOffset9`
    LD(Reg, PCOffset9),
    
    /// A LDI instruction.
    /// 
    /// # Operation
    /// 
    /// Computes an effective address (`mem[PC + PCOffset9]`), accesses the memory at that address,
    /// and stores it to the destination register (`DR`).
    /// This also sets the condition code for the LC-3 machine.
    /// 
    /// # Syntax
    /// - `LDI DR, PCOffset9`
    LDI(Reg, PCOffset9),
    
    /// A LDR instruction.
    /// 
    /// # Operation
    /// 
    /// Computes an effective address (`mem[BR + offset6]`), accesses the memory at that address,
    /// and stores it to the destination register (`DR`).
    /// This also sets the condition code for the LC-3 machine.
    /// 
    /// # Syntax
    /// - `LDR DR, BR, offset6`
    LDR(Reg, Reg, IOffset<6>),
    
    /// A LEA instruction.
    /// 
    /// # Operation
    /// 
    /// Computes an effective address (`PC + PCOffset9`) and stores it to the destination register (`DR`).
    /// 
    /// # Syntax
    /// - `LEA DR, PCOffset9`
    LEA(Reg, PCOffset9),

    /// A NOT instruction.
    /// 
    /// # Operation
    /// 
    /// Evaluates the operand, bitwise NOTs them, and stores the result to the destination register (`DR`).
    /// This also sets the condition code for the LC-3 machine.
    /// 
    /// # Syntax
    /// - `NOT DR, SR`
    NOT(Reg, Reg),
    
    /// A RET instruction.
    /// 
    /// # Operation
    /// 
    /// Returns from a subroutine. This is an alias for `JMP R7`.
    /// 
    /// # Syntax
    /// - `RET`
    RET,
    
    /// A RTI instruction.
    /// 
    /// # Operation
    /// 
    /// Returns from a trap or interrupt.
    /// 
    /// # Syntax
    /// - `RTI`
    RTI,
    
    /// A ST instruction.
    /// 
    /// # Operation
    /// 
    /// Computes an effective address (`PC + PCOffset9`), and writes the value from the source register (`SR`)
    /// into the memory at that address,
    /// 
    /// # Syntax
    /// - `ST SR, PCOffset9`
    ST(Reg, PCOffset9),

    /// A STI instruction.
    /// 
    /// # Operation
    /// 
    /// Computes an effective address (`mem[PC + PCOffset9]`), and writes the value from the source register (`SR`)
    /// into the memory at that address,
    /// 
    /// # Syntax
    /// - `STI SR, PCOffset9`
    STI(Reg, PCOffset9),

    /// A STR instruction.
    /// 
    /// # Operation
    /// 
    /// Computes an effective address (`mem[BR + offset6]`), and writes the value from the source register (`SR`)
    /// into the memory at that address,
    /// 
    /// # Syntax
    /// - `STR SR, BR, offset6`
    STR(Reg, Reg, IOffset<6>),

    /// A TRAP instruction.
    /// 
    /// # Operation
    /// 
    /// Executes the trap with the given trap vector `TrapVect8`.
    /// 
    /// # Syntax
    /// - `TRAP TrapVect8`
    TRAP(TrapVect8),

    /* ALIASES AND TRAPS */

    /// A NOP instruction.
    /// 
    /// # Operation
    /// 
    /// Does nothing.
    /// 
    /// # Syntax
    /// - `NOP`
    NOP,

    /// A GETC instruction.
    /// 
    /// # Operation
    /// 
    /// Gets a character from the keyboard, and store it into R0 (with the high 8 bits cleared). 
    /// This is an alias for `TRAP x20`.
    /// 
    /// # Syntax
    /// - `GETC`
    GETC,

    /// An OUT instruction.
    /// 
    /// # Operation
    /// 
    /// Writes a character from `R0[7:0]` to the display. This is an alias for `TRAP x21`.
    /// 
    /// # Syntax
    /// - `OUT`
    OUT,

    /// A PUTC instruction.
    /// 
    /// # Operation
    /// 
    /// Writes a character from `R0[7:0]` to the display. This is an alias for `TRAP x21`.
    /// 
    /// # Syntax
    /// - `PUTC`
    PUTC,

    /// A PUTS instruction.
    /// 
    /// # Operation
    /// 
    /// Prints characters in consecutive memory locations until a x00 character is read.
    /// This starts with the memory location pointed to by the address in `R0`.
    /// 
    /// This is an alias for `TRAP x22`.
    /// 
    /// # Syntax
    /// - `PUTS`
    PUTS,

    /// An IN instruction.
    /// 
    /// # Operation
    /// 
    /// Prompts the user for a character, stores the character into `R0` (with the high 8 bits cleared).
    /// Additionally, this prints the obtained character onto the display.
    /// 
    /// This is an alias for `TRAP x23`.
    /// 
    /// # Syntax
    /// - `IN`
    IN,

    /// A PUTSP instruction.
    /// 
    /// # Operation
    /// 
    /// Prints characters (two characters per memory location) until a x00 character is read.
    /// This starts with the memory location pointed to by the address in `R0`.
    /// This first prints the character in the low 8 bits, and then the character in the high 8 bits.
    /// 
    /// This is an alias for `TRAP x24`.
    /// 
    /// # Syntax
    /// - `PUTSP`
    PUTSP,

    /// A HALT instruction.
    /// 
    /// # Operation
    /// 
    /// Stops execution of the program. This is an alias for `TRAP x25`.
    /// 
    /// # Syntax
    /// - `HALT`
    HALT
}
impl std::fmt::Display for AsmInstr {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::ADD(dr, sr1, sr2) => write!(f, "ADD {dr}, {sr1}, {sr2}"),
            Self::AND(dr, sr1, sr2) => write!(f, "AND {dr}, {sr1}, {sr2}"),
            Self::BR(cc, off) => {
                write!(f, "BR")?;
                if cc & 0b100 != 0 { f.write_char('n')?; };
                if cc & 0b010 != 0 { f.write_char('z')?; };
                if cc & 0b001 != 0 { f.write_char('p')?; };
                write!(f, ", {off}")
            },
            Self::JMP(br) => write!(f, "JMP {br}"),
            Self::JSR(off) => write!(f, "JSR {off}"),
            Self::JSRR(br) => write!(f, "JSRR {br}"),
            Self::LD(dr, off) => write!(f, "LD {dr}, {off}"),
            Self::LDI(dr, off) => write!(f, "LDI {dr}, {off}"),
            Self::LDR(dr, br, off) => write!(f, "LDR {dr}, {br}, {off}"),
            Self::LEA(dr, off) => write!(f, "LEA {dr}, {off}"),
            Self::NOT(dr, sr) => write!(f, "NOT {dr}, {sr}"),
            Self::RET   => f.write_str("RET"),
            Self::RTI   => f.write_str("RTI"),
            Self::ST(sr, off) => write!(f, "ST {sr}, {off}"),
            Self::STI(sr, off) => write!(f, "STI {sr}, {off}"),
            Self::STR(sr, br, off) => write!(f, "STR {sr}, {br}, {off}"),
            Self::TRAP(vect) => write!(f, "TRAP {vect:02X}"),
            Self::NOP   => f.write_str("NOP"),
            Self::GETC  => f.write_str("GETC"),
            Self::OUT   => f.write_str("OUT"),
            Self::PUTC  => f.write_str("PUTC"),
            Self::PUTS  => f.write_str("PUTS"),
            Self::IN    => f.write_str("IN"),
            Self::PUTSP => f.write_str("PUTSP"),
            Self::HALT  => f.write_str("HALT"),
        }
    }
}

/// An enum representing all the possible directives in LC-3 assembly code.
pub enum Directive {
    /// An `.orig` directive.
    /// 
    /// # Operation
    /// 
    /// Starts a block of assembly.
    /// 
    /// # Syntax
    /// 
    /// `.orig ADDR`
    Orig(Offset<u16, 16>),

    /// A `.fill` directive.
    /// 
    /// # Operation
    /// 
    /// Writes some data into the given memory location.
    /// 
    /// # Syntax
    /// 
    /// `.fill DATA`
    /// `.fill LABEL`
    Fill(PCOffset<u16, 16>),
    
    
    /// A `.blkw` directive.
    /// 
    /// # Operation
    /// 
    /// Saves a provided number of memory locations for writing into.
    /// 
    /// # Syntax
    /// 
    /// `.blkw N`
    Blkw(Offset<u16, 16>),

    /// A `.stringz` directive.
    /// 
    /// # Operation
    /// 
    /// Writes a null-terminated string into the provided location.
    /// 
    /// # Syntax
    /// 
    /// `.stringz "A literal"`
    Stringz(String),

    /// A `.end` directive.
    /// 
    /// # Operation
    /// 
    /// Closes a block started by an `.orig`.
    /// 
    /// # Syntax
    /// 
    /// `.end`
    End,
    // External
}
impl std::fmt::Display for Directive {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Orig(addr)   => write!(f, ".orig {addr:04X}"),
            Self::Fill(val)    => write!(f, ".fill {val}"),
            Self::Blkw(n)      => write!(f, ".blkw {n}"),
            Self::Stringz(val) => write!(f, ".stringz {val:?}"),
            Self::End          => write!(f, ".end"),
        }
    }
}
enum StmtKind {
    Instr(AsmInstr),
    Directive(Directive)
}
struct Stmt {
    labels: Vec<String>,
    nucleus: StmtKind
}