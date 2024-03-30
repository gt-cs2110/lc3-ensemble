//! Memory handling for the LC-3 simulator.
//! 
//! This module consists of:
//! - [`Word`]: A mutable memory location.
//! - [`Mem`]: The memory.
//! - [`RegFile`]: The register file.

use crate::ast::Reg;

use super::{IODevice, SimErr, SimIO};

/// A memory location that can be read and written to.
/// 
/// # Reading
/// 
/// A word's value can be read with [`Word::get`]
/// to return its representation as an unsigned integer.
/// 
/// # Writing
/// 
/// A word can be written into with a value or with another word.
/// - [`Word::set`] to read a value into this word
/// - [`Word::copy_word`] to read a word into this word
/// 
/// [`Word::copy_word`] may be more useful in situations where initialization state may want to be preserved.
/// See the respective functions for more details.
/// 
/// Words can also be written to by applying assign operations (e.g., add, sub, and, etc.).
/// All arithmetic operations that can be applied to words are assumed to be wrapping.
/// See those implementations for more details.
#[derive(Debug, Clone, Copy)]
pub struct Word {
    data: u16,
    init: u16
}

const NO_BITS:  u16 = 0;
const ALL_BITS: u16 = 1u16.wrapping_neg();
impl Word {
    /// Creates a new word that is considered uninitialized.
    pub fn new_uninit() -> Self {
        Self {
            data: rand::random(),
            init: NO_BITS,
        }
    }
    /// Creates a new word that is initialized with a given data value.
    pub fn new_init(data: u16) -> Self {
        Self {
            data,
            init: ALL_BITS,
        }
    }

    /// Reads the word, returning its unsigned representation.
    pub fn get(&self) -> u16 {
        self.data
    }

    /// Checks that a word is fully initialized
    pub fn is_init(&self) -> bool {
        self.init == ALL_BITS
    }

    /// Writes to the word.
    /// 
    /// The data provided is assumed to be FULLY initialized,
    /// and will set the initialization state of this word to be
    /// fully initialized.
    /// 
    /// If the data is not fully initialized (e.g., if it is a partially initialized word),
    /// [`Word::copy_word`] can be used instead.
    pub fn set(&mut self, data: u16) {
        self.data = data;
        self.init = ALL_BITS;
    }
    /// Copies the data from one word into another.
    /// 
    /// This function is more cognizant of word initialization than [`Word::set`].
    /// - In non-strict mode, this function preserves the initialization data of the given word.
    /// - In strict mode, this function verifies the word copied is fully initialized, raising the provided error if not.
    pub fn copy_word(&mut self, word: Word, strict: bool, err: SimErr) -> Result<(), SimErr> {
        match !strict || word.is_init() {
            true => {
                *self = word;
                Ok(())
            },
            false => Err(err)
        }
    }
}
impl From<u16> for Word {
    /// Creates a fully initialized word.
    fn from(value: u16) -> Self {
        Word::new_init(value)
    }
}
impl From<i16> for Word {
    /// Creates a fully initialized word.
    fn from(value: i16) -> Self {
        Word::new_init(value as u16)
    }
}

impl std::ops::Not for Word {
    type Output = Word;

    /// Inverts the data on this word, preserving any initialization state.
    fn not(self) -> Self::Output {
        // Initialization state should stay the same after this.
        let Self { data, init } = self;
        Self { data: !data, init }
    }
}


impl std::ops::Add for Word {
    type Output = Word;

    /// Adds two words together (wrapping if overflow occurs).
    /// 
    /// If the two words are fully initialized, 
    /// the resulting word will also be fully initialized.
    /// Otherwise, the resulting word is fully uninitialized.
    fn add(self, rhs: Self) -> Self::Output {
        let Self { data: ldata, init: linit } = self;
        let Self { data: rdata, init: rinit } = rhs;

        if rdata == 0 && rinit == ALL_BITS { return self; }
        if ldata == 0 && linit == ALL_BITS { return rhs; }

        let data = ldata.wrapping_add(rdata);

        // Close enough calculation:
        // If both are fully init, consider this word fully init.
        // Otherwise, consider it fully uninit.
        let init = match linit == ALL_BITS && rinit == ALL_BITS {
            true  => ALL_BITS,
            false => NO_BITS,
        };

        Self { data, init }
    }
}
impl std::ops::AddAssign for Word {
    fn add_assign(&mut self, rhs: Self) {
        *self = *self + rhs;
    }
}
impl std::ops::AddAssign<u16> for Word {
    /// Increments the word by the provided value.
    /// 
    /// If the word was fully initialized,
    /// its updated value is also fully initialized.
    /// Otherwise, the resulting word is fully uninitialized.
    fn add_assign(&mut self, rhs: u16) {
        *self = *self + Word::from(rhs);
    }
}
impl std::ops::AddAssign<i16> for Word {
    /// Increments the word by the provided value.
    /// 
    /// If the word was fully initialized,
    /// its updated value is also fully initialized.
    /// Otherwise, the resulting word is fully uninitialized.
    fn add_assign(&mut self, rhs: i16) {
        *self = *self + Word::from(rhs);
    }
}


impl std::ops::Sub for Word {
    type Output = Word;

    /// Subtracts two words together (wrapping if overflow occurs).
    /// 
    /// If the two words are fully initialized, 
    /// the resulting word will also be fully initialized.
    /// Otherwise, the resulting word is fully uninitialized.
    fn sub(self, rhs: Self) -> Self::Output {
        let Self { data: ldata, init: linit } = self;
        let Self { data: rdata, init: rinit } = rhs;

        // This is (self - 0) == self.
        if rdata == 0 && rinit == ALL_BITS { return self; }

        let data = ldata.wrapping_sub(rdata);
        // Very lazy initialization scheme.
        // If both are fully init, consider this word fully init.
        // Otherwise, consider it fully uninit.
        let init = match linit == ALL_BITS && rinit == ALL_BITS {
            true  => ALL_BITS,
            false => NO_BITS,
        };

        Self { data, init }
    }
}
impl std::ops::SubAssign for Word {
    fn sub_assign(&mut self, rhs: Self) {
        *self = *self - rhs;
    }
}
impl std::ops::SubAssign<u16> for Word {
    /// Decrements the word by the provided value.
    /// 
    /// If the word was fully initialized,
    /// its updated value is also fully initialized.
    /// Otherwise, the resulting word is fully uninitialized.
    fn sub_assign(&mut self, rhs: u16) {
        *self = *self - Word::new_init(rhs);
    }
}
impl std::ops::SubAssign<i16> for Word {
    /// Decrements the word by the provided value.
    /// 
    /// If the word was fully initialized,
    /// its updated value is also fully initialized.
    /// Otherwise, the resulting word is fully uninitialized.
    fn sub_assign(&mut self, rhs: i16) {
        *self = *self - Word::new_init(rhs as _);
    }
}


impl std::ops::BitAnd for Word {
    type Output = Word;

    /// Applies a bitwise AND across two words.
    /// 
    /// This will also compute the correct initialization
    /// for the resulting word, taking into account bit clearing.
    fn bitand(self, rhs: Self) -> Self::Output {
        let Self { data: ldata, init: linit } = self;
        let Self { data: rdata, init: rinit } = rhs;

        let data = ldata & rdata;
        // A given bit of the result is init if:
        // - both the lhs and rhs bits are init
        // - either of the bits are data: 0, init: 1
        let init = (linit & rinit) | (!ldata & linit) | (!rdata & rinit);

        Self { data, init }
    }
}
impl std::ops::BitAndAssign for Word {
    fn bitand_assign(&mut self, rhs: Self) {
        *self = *self & rhs;
    }
}

pub(crate) trait AssertInit: Sized {
    fn is_initialized(&self) -> bool;
    fn assert_init<E>(self, strict: bool, err: E) -> Result<Self, E> {
        match !strict || self.is_initialized() {
            true  => Ok(self),
            false => Err(err),
        }
    }
}
impl AssertInit for &Word {
    fn is_initialized(&self) -> bool {
        self.is_init()
    }
}
impl AssertInit for &mut Word {
    fn is_initialized(&self) -> bool {
        self.is_init()
    }
}
impl AssertInit for Word {
    fn is_initialized(&self) -> bool {
        self.is_init()
    }
}

/// Context behind a memory access.
/// 
/// This struct is used by [`Mem::read`] and [`Mem::write`] to perform checks against memory accesses.
/// A default memory access context for the given simulator can be constructed with [`super::Simulator::default_mem_ctx`].
#[derive(Clone, Copy)]
pub struct MemAccessCtx {
    /// Whether this access is privileged (false = user, true = supervisor).
    pub privileged: bool,
    /// Whether writes to memory should follow strict rules 
    /// (no writing partially or fully uninitialized data).
    /// 
    /// This does not affect [`Mem::read`].
    pub strict: bool
}

const N: usize = 1 << 16;
const IO_START: u16 = 0xFE00;
const USER_RANGE: std::ops::Range<u16> = 0x3000..0xFE00;

/// Memory. This can be addressed with any `u16`.
#[derive(Debug)]
pub struct Mem {
    pub(super) data: Box<[Word; N]>,
    pub(super) io: SimIO
}
impl Mem {
    /// Creates a new memory with a provided initializer.
    fn create_with(initializer: impl FnMut() -> Word) -> Self {
        Self {
            data: std::iter::repeat_with(initializer)
                .take(N)
                .collect::<Box<_>>()
                .try_into()
                .unwrap_or_else(|_| unreachable!("iterator should have had {N} elements")),
            io: SimIO::Empty
        }
    }
    /// Creates a new memory with random, uninitialized values.
    pub fn new() -> Self {
        Self::create_with(Word::new_uninit)
    }

    /// Creates a new memory with zeroed (but initialized) values.
    pub fn zeroed() -> Self {
        Self::create_with(|| Word::new_init(0))
    }

    /// Copies a block into this memory.
    pub fn copy_block(&mut self, start: u16, data: &[Word]) {
        let mem = &mut self.data;
        let end = start.wrapping_add(data.len() as u16);
        if start <= end {
            // contiguous copy
            let range = (start as usize)..(end as usize);
            mem[range].copy_from_slice(data);
        } else {
            // discontiguous copy
            let len = start.wrapping_neg() as usize;
            let (left, right) = data.split_at(len);
            mem[(start as usize)..].copy_from_slice(left);
            mem[..(end as usize)].copy_from_slice(right);
        }
    }

    /// Gets a reference to a word from the memory's current state.
    /// 
    /// This is **only** meant to be used to query the state of the memory,
    /// not to simulate a read from memory.
    /// 
    /// Note the differences from [`Mem::read`]:
    /// - This function does not trigger IO effects (and as a result, IO values will not be updated).
    /// - This function does not require [`MemAccessCtx`].
    /// - This function does not perform access violation checks.
    /// 
    /// If any of these effects are necessary (e.g., when trying to execute instructions from the simulator),
    /// [`Mem::read`] should be used instead.
    pub fn get_raw(&self, addr: u16) -> &Word {
        // Mem could implement Index<u16>, but it doesn't as a lint against using this function incorrectly.
        &self.data[usize::from(addr)]
    }
    
    /// Gets a mutable reference to a word from the memory's current state.
    /// 
    /// This is **only** meant to be used to query/edit the state of the memory,
    /// not to simulate a write from memory.
    /// 
    /// Note the differences from [`Mem::write`]:
    /// - This function does not trigger IO effects (and as a result, IO values will not be updated).
    /// - This function does not require [`MemAccessCtx`].
    /// - This function does not perform access violation checks or strict uninitialized memory checking.
    /// 
    /// If any of these effects are necessary (e.g., when trying to execute instructions from the simulator),
    /// [`Mem::write`] should be used instead.
    pub fn get_raw_mut(&mut self, addr: u16) -> &mut Word {
        // Mem could implement IndexMut<u16>, but it doesn't as a lint against using this function incorrectly.
        &mut self.data[usize::from(addr)]
    }

    /// Fallibly reads the word at the provided index, erroring if not possible.
    /// 
    /// This accepts a [`MemAccessCtx`], that describes the parameters of the memory access.
    /// The simulator provides a default [`MemAccessCtx`] under [`super::Simulator::default_mem_ctx`].
    /// 
    /// The flags are used as follows:
    /// - `privileged`: if false, this access errors if the address is a memory location outside of the user range.
    /// - `strict`: not used for `read`
    /// 
    /// Note that this method is used for simulating a read. If you would like to query the memory's state, 
    /// consider [`Mem::get_raw`].
    pub fn read(&mut self, addr: u16, ctx: MemAccessCtx) -> Result<Word, SimErr> {
        if !ctx.privileged && !USER_RANGE.contains(&addr) { return Err(SimErr::AccessViolation) };

        if addr >= IO_START {
            if let Some(new_data) = self.io.io_read(addr) {
                self.data[usize::from(addr)].set(new_data);
            }
        }
        Ok(self.data[usize::from(addr)])
    }

    /// Fallibly writes the word at the provided index, erroring if not possible.
    /// 
    /// This accepts a [`MemAccessCtx`], that describes the parameters of the memory access.
    /// The simulator provides a default [`MemAccessCtx`] under [`super::Simulator::default_mem_ctx`].
    /// 
    /// The flags are used as follows:
    /// - `privileged`: if false, this access errors if the address is a memory location outside of the user range.
    /// - `strict`: If true, all accesses that would cause a memory location to be set with uninitialized data causes an error.
    /// 
    /// Note that this method is used for simulating a write. If you would like to edit the memory's state, 
    /// consider [`Mem::get_raw_mut`].
    pub fn write(&mut self, addr: u16, data: Word, ctx: MemAccessCtx) -> Result<(), SimErr> {
        if !ctx.privileged && !USER_RANGE.contains(&addr) { return Err(SimErr::AccessViolation) };
        
        let write_to_mem = if addr >= IO_START {
            let io_data = data.assert_init(ctx.strict, SimErr::StrictIOSetUninit)?
                .get();
            self.io.io_write(addr, io_data)
        } else {
            true
        };
        if write_to_mem {
            self.data[usize::from(addr)]
                .copy_word(data, ctx.strict, SimErr::StrictMemSetUninit)?;
        }
        Ok(())
    }
}
impl Default for Mem {
    fn default() -> Self {
        Self::new()
    }
}

/// The register file. 
/// 
/// This can be addressed with a [`Reg`], using typical array index notation.
#[derive(Debug, Clone)]
pub struct RegFile([Word; 8]);
impl RegFile {
    /// Creates a register file with uninitialized data.
    pub fn new() -> Self {
        Self(std::array::from_fn(|_| Word::new_uninit()))
    }

    /// Creates a register file with zeroed data.
    pub fn zeroed() -> Self {
        Self(std::array::from_fn(|_| Word::new_init(0)))
    }
}
impl std::ops::Index<Reg> for RegFile {
    type Output = Word;

    fn index(&self, index: Reg) -> &Self::Output {
        &self.0[usize::from(index)]
    }
}
impl std::ops::IndexMut<Reg> for RegFile {
    fn index_mut(&mut self, index: Reg) -> &mut Self::Output {
        &mut self.0[usize::from(index)]
    }
}
impl Default for RegFile {
    fn default() -> Self {
        Self::new()
    }
}