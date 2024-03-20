//! Writing an object file to an actual file.

use std::collections::{BTreeMap, HashMap};

use crate::sim::mem::Word;

use super::{ObjectFile, SymbolTable};

impl ObjectFile {
    /// Writes an object file into a Vec<u8>.
    pub fn write_bytes(&self) -> Vec<u8> {
        // Object file specification:
        // Data is divided into discrete chunks, which start with one of:
        // - 0x00: assembled bytecode block
        // - 0x01: label symbol table
        // - 0x02: line symbol table
        // 
        // Block 0x00 consists of:
        // - the identifier byte (1 byte)
        // - address where block starts (2 bytes)
        // - length of the block (2 bytes)
        // - the .orig span (16 bytes)
        // - the array of words (3n bytes)
        //    - each word is either 0xFF???? (initialized data) or 0x000000 (uninitialized data)
        //
        // Block 0x01 consists of:
        // - the identifier byte (1 byte)
        // - address of the label (2 bytes)
        // - the start of the label in source (8 bytes)
        // - the length of the label's name (8 bytes)
        // - the label (n bytes)
        //
        // Block 0x02 consists of:
        // - the identifier byte (1 byte)
        // - the source line number (8 bytes)
        // - length of contiguous block (2 bytes)
        // - the contiguous block (2n bytes)
        
        let mut bytes = vec![];
        for (&addr, (data, orig_span)) in self.block_map.iter() {
            bytes.push(0x00);
            bytes.extend(u16::to_le_bytes(addr));
            bytes.extend(u16::to_le_bytes(data.len() as u16));
            bytes.extend(u64::to_le_bytes(orig_span.start as u64));
            bytes.extend(u64::to_le_bytes(orig_span.end as u64));
            for word in data {
                if word.is_init() {
                    bytes.push(0xFF);
                    bytes.extend(u16::to_le_bytes(word.get()));
                } else {
                    bytes.extend([0x00; 3]);
                }
            }
        }

        if let Some(sym) = &self.sym {
            for (label, &(addr, span_start)) in sym.labels.iter() {
                bytes.push(0x01);
                bytes.extend(u16::to_le_bytes(addr));
                bytes.extend(u64::to_le_bytes(span_start as u64));
                bytes.extend(u64::to_le_bytes(label.len() as u64));
                bytes.extend_from_slice(label.as_bytes());
            }

            for (lno, data) in sym.lines.0.iter() {
                bytes.push(0x02);
                bytes.extend(u64::to_le_bytes(*lno as u64));
                bytes.extend(u16::to_le_bytes(data.len() as u16));
                for &word in data {
                    bytes.extend(u16::to_le_bytes(word));
                }
            }
        }
        bytes
    }

    /// Reads a Vec<u8> back into object file information.
    pub fn read_bytes(mut vec: &[u8]) -> Option<ObjectFile> {
        let mut block_map   = BTreeMap::new();
        let mut label_table = HashMap::new();
        let mut line_table  = vec![];

        while !vec.is_empty() {
            let Some((ident_byte, rest)) = vec.split_first() else { unreachable!() };
            vec = rest;
            match ident_byte {
                0x00 => {
                    let addr            = u16::from_le_bytes(take::<2>(&mut vec)?);
                    let data_len        = u16::from_le_bytes(take::<2>(&mut vec)?);
                    let orig_span_start = u64::from_le_bytes(take::<8>(&mut vec)?) as usize;
                    let orig_span_end   = u64::from_le_bytes(take::<8>(&mut vec)?) as usize;

                    let orig_span = orig_span_start..orig_span_end;
                    let data = map_chunks::<_, 3>(take_slice(&mut vec, 3 * usize::from(data_len))?, |[init, rest @ ..]| match init != 0 {
                        true  => Word::new_init(u16::from_le_bytes(rest)),
                        false => Word::new_uninit(),
                    });

                    block_map.insert(addr, (data, orig_span));
                },
                0x01 => {
                    let addr       = u16::from_le_bytes(take::<2>(&mut vec)?);
                    let span_start = u64::from_le_bytes(take::<8>(&mut vec)?) as usize;
                    let str_len    = u64::from_le_bytes(take::<8>(&mut vec)?) as usize;
                    let string     = String::from_utf8(take_slice(&mut vec, str_len)?.to_vec()).ok()?;

                    label_table.insert(string, (addr, span_start));
                },
                0x02 => {
                    let lno      = u64::from_le_bytes(take::<8>(&mut vec)?) as usize;
                    let data_len = u16::from_le_bytes(take::<2>(&mut vec)?);
                    let data     = map_chunks::<_, 2>(take_slice(&mut vec, 2 * usize::from(data_len))?, u16::from_le_bytes);
                    
                    line_table.push((lno, data));
                },
                _ => return None
            }
        }

        let sym = match !label_table.is_empty() || !line_table.is_empty() {
            true  => Some(SymbolTable {
                labels: label_table,
                lines:  super::LineSymbolTable(line_table),
            }),
            false => None,
        };
        Some(ObjectFile {
            block_map,
            sym,
        })
    }
}

fn take<const N: usize>(data: &mut &[u8]) -> Option<[u8; N]> {
    take_slice(data, N)
        .map(|slice| <[_; N]>::try_from(slice).unwrap())
}
fn take_slice<'a>(data: &mut &'a [u8], n: usize) -> Option<&'a [u8]> {
    let (left, right) = try_split_at(data, n)?;
    *data = right;
    Some(left)
}
fn try_split_at(data: &[u8], n: usize) -> Option<(&[u8], &[u8])> {
    if n > data.len() { return None; }
    Some(data.split_at(n))
}
fn map_chunks<T, const N: usize>(data: &[u8], f: impl FnMut([u8; N]) -> T) -> Vec<T> {
    assert_eq!(data.len() % N, 0);
    
    data.chunks_exact(N)
        .map(|c| <[_; N]>::try_from(c).unwrap())
        .map(f)
        .collect()
}