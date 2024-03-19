//! Assembling assembly source ASTs into object files.
//! 
//! This module is used to convert source ASTs (`Vec<`[`Stmt`]`>`) into object files 
//! that can be executed by the simulator.
//! 
//! The assembler module notably consists of:
//! - [`assemble`]: The main function which assembles the statements into an object file.
//! - [`SymbolTable`]: a struct holding the symbol table, which stores location information for labels after the first assembler pass
//! - [`ObjectFile`]: a struct holding the object file, which can be loaded into the simulator and executed
//! 
//! [`Stmt`]: crate::ast::asm::Stmt

use std::collections::hash_map::Entry;
use std::collections::{BTreeMap, HashMap};

use crate::ast::asm::{AsmInstr, Directive, Stmt, StmtKind};
use crate::ast::sim::SimInstr;
use crate::ast::{IOffset, ImmOrReg, Offset, OffsetNewErr, PCOffset, Reg};
use crate::sim::mem::Word;


/// Assembles a assembly source code AST into an object file.
pub fn assemble(ast: Vec<Stmt>) -> Result<ObjectFile, AsmErr> {
    let sym = SymbolTable::new(&ast)?;
    let mut obj = ObjectFile::new();

    // PASS 2
    // Holding both the LC and currently writing block
    let mut current: Option<(u16, ObjBlock)> = None;

    for stmt in ast {
        match stmt.nucleus {
            StmtKind::Directive(Directive::Orig(off)) => {
                // Add new working block.
                debug_assert!(current.is_none());
                
                let addr = off.get();
                current.replace((addr + 1, ObjBlock { start: addr, words: vec![] }));
            },
            StmtKind::Directive(Directive::End) => {
                // The current block is complete, so take it out and push it into the object file.
                let Some((_, ObjBlock { start, words })) = current.take() else {
                    return Err(AsmErr::UnopenedOrig); // unreachable (because pass 1 should've found it)
                };
                obj.push(start, words)?;
            },
            StmtKind::Directive(directive) => {
                let Some((lc, block)) = &mut current else { return Err(AsmErr::UndetAddrStmt) };
                let n = directive.write_directive(&sym, block)?;
                *lc = lc.wrapping_add(n);
            },
            StmtKind::Instr(instr) => {
                let Some((lc, block)) = &mut current else { return Err(AsmErr::UndetAddrStmt) };
                let sim = instr.into_sim_instr(*lc, &sym)?;
                block.push(sim.encode());
                *lc = lc.wrapping_add(1);
            },
        }
    }

    Ok(obj)
}
/// Error from assembling given assembly code.
#[derive(Debug)]
pub enum AsmErr {
    /// Cannot determine address of label (pass 1).
    UndetAddrLabel,
    /// Cannot determine address of instruction (pass 2).
    UndetAddrStmt,
    /// There was an `.orig` but no corresponding `.end` (pass 1).
    UnclosedOrig,
    /// There was an `.end` but no corresonding `.orig` (pass 1).
    UnopenedOrig,
    /// There was an `.orig` opened after another `.orig` (pass 1).
    OverlappingOrig,
    /// There were multiple labels of the same name (pass 1).
    OverlappingLabels,
    /// There are blocks that overlap ranges of memory (pass 2).
    OverlappingBlocks,
    /// Creating the offset to replace a label caused overflow (pass 2).
    OffsetNewErr(OffsetNewErr),
    /// Label did not have an assigned address (pass 2).
    CouldNotFindLabel,
    /// Block is way too large (pass 2).
    ExcessiveBlock,
}
impl std::fmt::Display for AsmErr {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            AsmErr::UndetAddrLabel    => f.write_str("cannot determine address of label"),
            AsmErr::UndetAddrStmt     => f.write_str("cannot determine address of statement"),
            AsmErr::UnclosedOrig      => f.write_str(".orig directive was never closed"),
            AsmErr::UnopenedOrig      => f.write_str(".end does not have associated .orig"),
            AsmErr::OverlappingOrig   => f.write_str("cannot have an .orig inside another region"),
            AsmErr::OverlappingLabels => f.write_str("label was defined multiple times"),
            AsmErr::OverlappingBlocks => f.write_str("regions would overlap in memory"),
            AsmErr::OffsetNewErr(e)   => e.fmt(f),
            AsmErr::CouldNotFindLabel => f.write_str("label does not exist"),
            AsmErr::ExcessiveBlock    => f.write_str("block is too large"),
        }
    }
}
impl std::error::Error for AsmErr {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match self {
            Self::OffsetNewErr(e) => Some(e),
            _ => None
        }
    }
}
impl crate::err::Error for AsmErr {
    fn help(&self) -> Option<std::borrow::Cow<str>> {
        match self {
            AsmErr::UndetAddrLabel    => Some("try moving this label inside of a .orig/.end region".into()),
            AsmErr::UndetAddrStmt     => Some("try moving this statement inside of a .orig/.end region".into()),
            AsmErr::UnclosedOrig      => None,
            AsmErr::UnopenedOrig      => None,
            AsmErr::OverlappingOrig   => None,
            AsmErr::OverlappingLabels => Some("labels must be unique within a file, try renaming one of the labels".into()),
            AsmErr::OverlappingBlocks => None,
            AsmErr::OffsetNewErr(e)   => e.help(),
            AsmErr::CouldNotFindLabel => None,
            AsmErr::ExcessiveBlock    => None,
        }
    }
}
/// The symbol table created in the first assembler pass
/// that maps each label to its corresponding address.
#[derive(Debug, PartialEq, Eq)]
pub struct SymbolTable {
    /// A mapping from label to address.
    labels: HashMap<String, u16>
}

impl SymbolTable {
    /// Creates a new symbol table (performing the first assembler pass)
    /// by reading through the statements and computing label addresses.
    pub fn new(stmts: &[Stmt]) -> Result<Self, AsmErr> {
        let mut lc: Option<u16> = None;
        let mut labels = HashMap::new();

        for stmt in stmts {
            // Add labels if they exist
            if !stmt.labels.is_empty() {
                let Some(addr) = lc else { return Err(AsmErr::UndetAddrLabel) };

                for label in &stmt.labels {
                    match labels.entry(label.to_uppercase()) {
                        Entry::Occupied(_) => return Err(AsmErr::OverlappingLabels),
                        Entry::Vacant(e) => e.insert(addr),
                    };
                }
            }

            lc = match &stmt.nucleus {
                StmtKind::Instr(_) => lc.map(|addr| addr.wrapping_add(1)),
                StmtKind::Directive(d) => match d {
                    Directive::Orig(addr) => match lc {
                        Some(_) => return Err(AsmErr::OverlappingOrig),
                        None => Some(addr.get())
                    },
                    Directive::Fill(_) => lc.map(|addr| addr.wrapping_add(1)),
                    Directive::Blkw(n) => lc.map(|addr| addr.wrapping_add(n.get())),
                    Directive::Stringz(s) => lc.map(|addr| addr.wrapping_add(s.len() as u16).wrapping_add(1)),
                    Directive::End => match lc {
                        Some(_) => None,
                        None => return Err(AsmErr::UnopenedOrig)
                    },
                },
            };
        }

        match lc {
            None    => Ok(SymbolTable { labels }),
            Some(_) => Err(AsmErr::UnclosedOrig),
        }
    }

    /// Gets the address of a given label (if it exists).
    pub fn get(&self, label: &str) -> Option<u16> {
        self.labels.get(&label.to_uppercase()).copied()
    }
}


/// Replaces a [`PCOffset`] value with an [`Offset`] value by calculating the offset from a given label
/// (if this `PCOffset` represents a label).
fn replace_pc_offset<const N: u32>(off: PCOffset<i16, N>, lc: u16, sym: &SymbolTable) -> Result<IOffset<N>, AsmErr> {
    match off {
        PCOffset::Offset(off) => Ok(off),
        PCOffset::Label(label) => {
            let Some(loc) = sym.get(&label) else { return Err(AsmErr::CouldNotFindLabel) };
            IOffset::new(loc.wrapping_sub(lc) as i16)
                .map_err(AsmErr::OffsetNewErr)
        },
    }
}

impl AsmInstr {
    /// Converts an ASM instruction into a simulator instruction ([`SimInstr`])
    /// by resolving offsets and erasing aliases.
    pub fn into_sim_instr(self, lc: u16, sym: &SymbolTable) -> Result<SimInstr, AsmErr> {
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
            AsmInstr::NOP(off)          => Ok(SimInstr::BR(0b000, replace_pc_offset(off, lc, sym)?)),
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
impl Directive {
    /// Writes the assembly for the given directive into the provided object block.
    /// 
    /// This also returns the total number of memory locations written.
    fn write_directive(self, labels: &SymbolTable, block: &mut ObjBlock) -> Result<u16, AsmErr> {
        match self {
            Directive::Orig(_) => Ok(0),
            Directive::Fill(pc_offset) => {
                let off = match pc_offset {
                    PCOffset::Offset(o) => o.get(),
                    PCOffset::Label(l)  => labels.get(&l).ok_or(AsmErr::CouldNotFindLabel)?,
                };

                block.push(off);
                Ok(1)
            },
            Directive::Blkw(n) => {
                block.shift(n.get());
                Ok(n.get())
            },
            Directive::Stringz(n) => {
                block.extend(n.bytes().map(u16::from));
                block.push(0);
                Ok((n.len() as u16).wrapping_add(1))
            },
            Directive::End => Ok(0),
        }
    }
}

/// A singular block which represents a singular region in an object file.
struct ObjBlock {
    /// Starting address of the block.
    start: u16,
    /// The words in the block.
    words: Vec<Word>
}
impl ObjBlock {
    fn push(&mut self, data: u16) {
        self.words.push(Word::new_init(data));
    }
    fn shift(&mut self, n: u16) {
        self.words.extend({
            std::iter::repeat_with(Word::new_uninit)
                .take(usize::from(n))
        });
    }
}
impl Extend<u16> for ObjBlock {
    fn extend<T: IntoIterator<Item = u16>>(&mut self, iter: T) {
        self.words.extend(iter.into_iter().map(Word::new_init));
    }
}

/// An object file.
/// 
/// This is the final product after assembly source code is fully assembled.
/// This can be loaded in the simulator to run the assembled code.
#[derive(Debug)]
pub struct ObjectFile {
    /// A mapping from address to the words written starting from that address.
    block_map: BTreeMap<u16, Vec<Word>>
}
impl ObjectFile {
    /// Creates a new, empty [`ObjectFile`].
    pub fn new() -> Self {
        ObjectFile {
            block_map: BTreeMap::new()
        }
    }

    /// Add a new block to the object file, writing the provided words (`words`) at the provided address (`start`).
    /// 
    /// This will error if this block overlaps with another block already present in the object file.
    pub fn push(&mut self, start: u16, words: Vec<Word>) -> Result<(), AsmErr> {
        // Only add to object file if non-empty:
        if !words.is_empty() {
            // Check block size to make sure block doesn't wrap around itself
            if words.len() > (1 << u16::BITS) {
                return Err(AsmErr::ExcessiveBlock);
            }

            // Find previous block and ensure no overlap:
            let prev_block = self.block_map.range(..=start).next_back()
                .or_else(|| self.block_map.last_key_value());

            if let Some((&prev_start, prev_words)) = prev_block {
                // check if this block overlaps with the previous block
                if (start.wrapping_sub(prev_start) as usize) < prev_words.len() {
                    return Err(AsmErr::OverlappingBlocks);
                }
            }

            // No overlap, so we can add it:
            self.block_map.insert(start, words);
        }

        Ok(())
    }

    /// Get an iterator over all of the blocks of the object file.
    pub fn iter(&self) -> ObjFileIter<'_> {
        self.block_map.iter()
    }
}

type ObjFileIter<'o> = std::collections::btree_map::Iter<'o, u16, Vec<Word>>;
impl<'o> IntoIterator for &'o ObjectFile {
    type Item = <Self::IntoIter as Iterator>::Item;
    type IntoIter = ObjFileIter<'o>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}
impl Default for ObjectFile {
    fn default() -> Self {
        Self::new()
    }
}