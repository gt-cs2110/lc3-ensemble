//! Assembling assembly source ASTs into object files.
//! 
//! This module is used to convert source ASTs (`Vec<`[`Stmt`]`>`) into object files 
//! that can be executed by the simulator.
//! 
//! The assembler module notably consists of:
//! - [`Assembler`]: a struct which performs assembler passes on a source AST and produces an object file
//! - [`SymbolTable`]: a struct holding the symbol table, which stores location information for labels after the first assembler pass
//! - [`ObjectFile`]: a struct holding the object file, which can be loaded into the simulator and executed
//! 
//! [`Stmt`]: crate::ast::asm::Stmt

use std::collections::hash_map::Entry;
use std::collections::{BTreeMap, HashMap};

use crate::ast::asm::{AsmInstr, Directive, Stmt, StmtKind};
use crate::ast::sim::SimInstr;
use crate::ast::{IOffset, ImmOrReg, Offset, OffsetNewErr, PCOffset, Reg};
use crate::sim::Word;


/// Error from assembling given assembly code.
#[derive(Debug)]
pub enum AsmErr {
    /// Cannot determine address of label or instruction (pass 1 and 2).
    CannotDetAddress,
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
    CouldNotFindLabel
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
                let Some(addr) = lc else { return Err(AsmErr::CannotDetAddress) };

                for label in &stmt.labels {
                    match labels.entry(label.to_string()) {
                        Entry::Occupied(_) => return Err(AsmErr::OverlappingLabels),
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
impl Directive {
    fn write_directive(self, labels: &SymbolTable, block: &mut ObjBlock) -> Result<(), AsmErr> {
        match self {
            Directive::Orig(_) => {},
            Directive::Fill(pc_offset) => {
                let off = match pc_offset {
                    PCOffset::Offset(o) => o.get(),
                    PCOffset::Label(l)  => labels.get(&l).ok_or(AsmErr::CouldNotFindLabel)?,
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

/// The assembler! Converts assembly statements into bytecode.
#[derive(Debug)]
pub struct Assembler {
    /// The statements to convert.
    stmts: Vec<Stmt>,
    /// The symbol table of the statements (computed on initialization)
    sym: SymbolTable,
    /// The object file produced as a result
    obj: ObjectFile
}
impl Assembler {
    /// Creates a new assembler (and runs the first pass).
    pub fn new(stmts: Vec<Stmt>) -> Result<Self, AsmErr> {
        let sym = SymbolTable::new(&stmts)?;
        Ok(Self { stmts, sym, obj: ObjectFile::new() })
    }

    /// Creates the object file (and returns any errors that result from it).
    pub fn prepare_obj_file(&mut self) -> Result<(), AsmErr> {
        // Holding both the LC and currently writing block
        let mut current: Option<(u16, ObjBlock)> = None;

        for stmt in std::mem::take(&mut self.stmts) {
            if let Some((lc, _)) = current.as_mut() {
                *lc = lc.wrapping_add(1);
            }

            match stmt.nucleus {
                StmtKind::Directive(Directive::Orig(off)) => {
                    // Add new working block.
                    debug_assert!(current.is_none());
                    let addr = off.get();
                    current.replace((addr, ObjBlock { start: addr, words: vec![] }));
                },
                StmtKind::Directive(Directive::End) => {
                    // Take out the current working block and put it into completed blocks.
                    let Some((_, ObjBlock { start, words })) = current.take() else {
                        return Err(AsmErr::UnopenedOrig); // unreachable (because pass 1 should've found it)
                    };
                    self.obj.push(start, words)?;
                },
                StmtKind::Directive(directive) => {
                    let Some((_, block)) = &mut current else { return Err(AsmErr::CannotDetAddress) };
                    directive.write_directive(&self.sym, block)?;
                },
                StmtKind::Instr(instr) => {
                    let Some((lc, block)) = &mut current else { return Err(AsmErr::CannotDetAddress) };
                    let sim = instr.into_sim_instr(*lc, &self.sym)?;
                    block.push(sim.encode());
                },
            }
        }

        Ok(())
    }

    /// Gets the produced object file.
    pub fn unwrap(self) -> ObjectFile {
        self.obj
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
            std::iter::from_fn(|| Some(Word::new_uninit()))
                .take(n as usize)
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
            // Find previous block and ensure no overlap:
            let prev_block = self.block_map.range(..start).next_back()
                .or_else(|| self.block_map.last_key_value());

            if let Some((&addr, block_words)) = prev_block {
                // check if this block overlaps with the previous block
                if (start.wrapping_sub(addr) as usize) < block_words.len() {
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