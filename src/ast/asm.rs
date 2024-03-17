//! This module is used for holding simulation instructions ([`Self`]),
//! which are instructions that directly map to assembly code.
//! 
//! For instructions that map bytecode, see [`sim::SimInstr`].
//! 
//! [`sim::SimInstr`]: [`crate::ast::sim::SimInstr`]

use std::collections::hash_map::Entry;
use std::collections::HashMap;
use std::fmt::Write as _;

use super::sim::{CodegenError, SimBlock, SimInstr};
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
impl AsmInstr {
    fn into_sim_instr(self, lc: u16, sym: &SymbolTable) -> Result<SimInstr, CodegenError> {
        match self {
            AsmInstr::ADD(dr, sr1, sr2) => Ok(SimInstr::ADD(dr, sr1, sr2)),
            AsmInstr::AND(dr, sr1, sr2) => Ok(SimInstr::AND(dr, sr1, sr2)),
            AsmInstr::BR(cc, off)       => Ok(SimInstr::BR(cc, replace_pc_offset(off, lc, sym)?)),
            AsmInstr::JMP(br)           => Ok(SimInstr::JMP(br)),
            AsmInstr::JSR(off)          => Ok(SimInstr::JSR(ImmOrReg::Imm(replace_pc_offset(off, lc, sym)?))),
            AsmInstr::JSRR(br)          => Ok(SimInstr::JSR(ImmOrReg::Reg(br))),
            AsmInstr::LD(dr, off)       => Ok(SimInstr::LD(dr, replace_pc_offset(off, lc, sym)?)),
            AsmInstr::LDI(dr, off)      => Ok(SimInstr::LDI(dr, replace_pc_offset(off, lc, sym)?)),
            AsmInstr::LDR(dr, br, off)  => Ok(SimInstr::LDR(dr, br, off)),
            AsmInstr::LEA(dr, off)      => Ok(SimInstr::LEA(dr, replace_pc_offset(off, lc, sym)?)),
            AsmInstr::NOT(dr, sr)       => Ok(SimInstr::NOT(dr, sr)),
            AsmInstr::RET               => Ok(SimInstr::JMP(Reg(0b111))),
            AsmInstr::RTI               => Ok(SimInstr::RTI),
            AsmInstr::ST(sr, off)       => Ok(SimInstr::ST(sr, replace_pc_offset(off, lc, sym)?)),
            AsmInstr::STI(sr, off)      => Ok(SimInstr::STI(sr, replace_pc_offset(off, lc, sym)?)),
            AsmInstr::STR(sr, br, off)  => Ok(SimInstr::STR(sr, br, off)),
            AsmInstr::TRAP(vect)        => Ok(SimInstr::TRAP(vect)),
            AsmInstr::NOP               => Ok(SimInstr::BR(0b111, Offset::new_trunc(-1))),
            AsmInstr::GETC              => Ok(SimInstr::TRAP(Offset::new_trunc(0x20))),
            AsmInstr::OUT               => Ok(SimInstr::TRAP(Offset::new_trunc(0x21))),
            AsmInstr::PUTC              => Ok(SimInstr::TRAP(Offset::new_trunc(0x21))),
            AsmInstr::PUTS              => Ok(SimInstr::TRAP(Offset::new_trunc(0x22))),
            AsmInstr::IN                => Ok(SimInstr::TRAP(Offset::new_trunc(0x23))),
            AsmInstr::PUTSP             => Ok(SimInstr::TRAP(Offset::new_trunc(0x24))),
            AsmInstr::HALT              => Ok(SimInstr::TRAP(Offset::new_trunc(0x25))),
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
impl Directive {
    fn write_directive(self, labels: &SymbolTable, block: &mut SimBlock) -> Result<(), CodegenError> {
        match self {
            Directive::Orig(_) => {},
            Directive::Fill(pc_offset) => {
                let off = match pc_offset {
                    PCOffset::Offset(o) => o.get(),
                    PCOffset::Label(l)  => labels.get(&l).ok_or(CodegenError::CouldNotFindLabel)?,
                };

                block.push(off);
            },
            Directive::Blkw(n) => {
                block.shift(n.get());
            },
            Directive::Stringz(n) => {
                block.extend(n.bytes().map(u16::from));
                block.push(0);
            },
            Directive::End => {},
        };

        Ok(())
    }
}

/// Either an instruction or a directive.
pub enum StmtKind {
    #[allow(missing_docs)]
    Instr(AsmInstr),
    #[allow(missing_docs)]
    Directive(Directive)
}

/// An instruction or directive and the labels associated with them.
pub struct Stmt {
    /// The labels.
    pub labels: Vec<String>,
    /// The instruction or directive.
    pub nucleus: StmtKind
}

/// The symbol table that maps each label to its corresponding address.
pub struct SymbolTable {
    labels: HashMap<String, u16>
}

/// Error from creating the symbol table.
pub enum PassError {
    /// Cannot determine address of label.
    CannotDetAddress,
    /// There was an `.orig` but no corresponding `.end`.
    UnclosedOrig,
    /// There was an `.end` but no corresonding `.orig`.
    UnopenedOrig,
    /// There was an `.orig` opened after another `.orig`.
    OverlappingOrig,
    /// There were multiple labels of the same name.
    OverlappingLabels
}
impl SymbolTable {
    fn new(stmts: &[Stmt]) -> Result<Self, PassError> {
        let mut lc: Option<u16> = None;
        let mut labels = HashMap::new();

        for stmt in stmts {
            // Add labels if they exist
            if !stmt.labels.is_empty() {
                let Some(addr) = lc else { return Err(PassError::CannotDetAddress) };

                for label in &stmt.labels {
                    match labels.entry(label.to_string()) {
                        Entry::Occupied(_) => return Err(PassError::OverlappingLabels),
                        Entry::Vacant(e) => e.insert(addr),
                    };
                }
                labels.extend({
                    stmt.labels.iter()
                        .map(|label| (label.to_uppercase(), addr))
                });
            }

            lc = match &stmt.nucleus {
                StmtKind::Instr(_) => lc.map(|addr| addr.wrapping_add(1)),
                StmtKind::Directive(d) => match d {
                    Directive::Orig(addr) => match lc {
                        Some(_) => return Err(PassError::OverlappingOrig),
                        None => Some(addr.get())
                    },
                    Directive::Fill(_) => lc.map(|addr| addr.wrapping_add(1)),
                    Directive::Blkw(n) => lc.map(|addr| addr.wrapping_add(n.get())),
                    Directive::Stringz(s) => lc.map(|addr| addr.wrapping_add(s.len() as u16).wrapping_add(1)),
                    Directive::End => match lc {
                        Some(_) => None,
                        None => return Err(PassError::UnopenedOrig)
                    },
                },
            };
        }

        match lc {
            None    => Ok(SymbolTable { labels }),
            Some(_) => Err(PassError::UnclosedOrig),
        }
    }

    fn get(&self, label: &str) -> Option<u16> {
        self.labels.get(&label.to_uppercase()).cloned()
    }
}

fn replace_pc_offset<const N: u32>(off: PCOffset<i16, N>, lc: u16, sym: &SymbolTable) -> Result<Offset<i16, N>, CodegenError> {
    match off {
        PCOffset::Offset(off) => Ok(off),
        PCOffset::Label(label) => {
            let Some(loc) = sym.get(&label) else { return Err(CodegenError::CouldNotFindLabel) };
            Offset::new(loc.wrapping_sub(lc) as i16)
                .map_err(CodegenError::OffsetNewError)
        },
    }
}

fn create_sim_blocks(stmts: Vec<Stmt>, sym: &SymbolTable) -> Result<Vec<SimBlock>, CodegenError> {
    // Holding both the LC and currently writing block
    let mut current: Option<(u16, SimBlock)> = None;
    // Holding all blocks that have been written to
    let mut blocks = vec![];

    for stmt in stmts {
        if let Some((lc, _)) = current.as_mut() {
            *lc = lc.wrapping_add(1);
        }

        match stmt.nucleus {
            StmtKind::Directive(Directive::Orig(off)) => {
                // Add new working block.
                debug_assert!(current.is_none());
                let addr = off.get();
                current.replace((addr, SimBlock { start: addr, words: vec![] }));
            },
            StmtKind::Directive(Directive::End) => {
                // Take out the current working block and put it into completed blocks.
                let Some((_, block)) = current.take() else { unreachable!("pass 1 verified valid .orig/.end pairs") };
                blocks.push(block);
            },
            StmtKind::Directive(directive) => {
                let Some((_, block)) = &mut current else { return Err(CodegenError::CannotDetAddress) };
                directive.write_directive(sym, block)?;
            },
            StmtKind::Instr(instr) => {
                let Some((lc, block)) = &mut current else { return Err(CodegenError::CannotDetAddress) };
                let sim = instr.into_sim_instr(*lc, sym)?;
                block.push(sim.encode());
            },
        }
    }

    Ok(blocks)
}