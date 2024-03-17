//! Individual memory cells ([`Word`]s).
//! 
//! This module consists of:
//! - [`Word`]: A mutable memory location
//! - [`WordArray`]: An array of memory locations, which can be indexed with non-usize types

/// A memory location that can be read and written to.
/// 
/// # Reading
/// 
/// A word can be read as either an unsigned integer or a signed one.
/// - [`Word::get_unsigned`] to read the word as unsigned
/// - [`Word::get_signed`] to read the word as signed
/// 
/// # Writing
/// 
/// A word can be written into with a value or with another word.
/// - [`Word::set`] to read a value into this word
/// - [`Word::copy_word`] to read a word into this word
/// 
/// `copy_word` may be more useful in situations where initialization state may want to be preserved.
/// See [`Word::set`] for more details.
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
            data: 0,
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
    pub fn get_unsigned(&self) -> u16 {
        self.data
    }
    /// Reads the word, returning its signed representation.
    pub fn get_signed(&self) -> i16 {
        self.data as i16
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
    /// This is useful for preserving initialization state.
    pub fn copy_word(&mut self, word: Word) {
        *self = word;
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

/** NOT **/
impl std::ops::Not for Word {
    type Output = Word;

    /// Inverts the data on this word, preserving any initialization state.
    fn not(self) -> Self::Output {
        // Initialization state should stay the same after this.
        let Self { data, init } = self;
        Self { data: !data, init }
    }
}

/** ADD **/
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

        let data = ldata.wrapping_add(rdata);
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

/** SUB **/
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

/** AND **/
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

/// Backing type for a word array.
pub trait ArrayBacking: Sized {
    /// Gets a reference to the entire slice of words.
    fn slice(&self) -> &[Word];
    /// Gets a mutable reference to the entire slice of words.
    fn slice_mut(&mut self) -> &mut [Word];
    /// Constructs a new backing.
    fn new() -> Self;
}
impl<const N: usize> ArrayBacking for [Word; N] {
    fn slice(&self) -> &[Word] {
        self
    }

    fn slice_mut(&mut self) -> &mut [Word] {
        self
    }

    fn new() -> Self {
        std::array::from_fn(|_| Word::new_uninit())
    }
}
impl<const N: usize> ArrayBacking for Box<[Word; N]> {
    fn slice(&self) -> &[Word] {
        &**self
    }

    fn slice_mut(&mut self) -> &mut [Word] {
        &mut **self
    }

    fn new() -> Self {
        std::iter::repeat_with(Word::new_uninit)
            .take(N)
            .collect::<Vec<_>>()
            .try_into()
            .unwrap_or_else(|_| unreachable!("exactly {N} words were created"))
    }
}


/// Similar to type `[Word; _]`, but also allows indices of types smaller than usize.
/// 
/// This is used with the register file to make an array indexable with `Reg`,
/// and with the memory to make an array indexable with `u16`.
#[repr(transparent)]
pub struct WordArray<A, I>(A, std::marker::PhantomData<I>);
impl<A: ArrayBacking, I: Into<usize>> WordArray<A, I> {
    /// Creates a new word array with uninitialized memory.
    pub fn new() -> Self {
        Self(A::new(), std::marker::PhantomData)
    }
}
impl<A: ArrayBacking, I: Into<usize>> Default for WordArray<A, I> {
    fn default() -> Self {
        Self::new()
    }
}
impl<A: ArrayBacking, I: Into<usize>> std::ops::Index<I> for WordArray<A, I> {
    type Output = Word;

    fn index(&self, index: I) -> &Self::Output {
        &self.0.slice()[index.into()]
    }
}
impl<A: ArrayBacking, I: Into<usize>> std::ops::IndexMut<I> for WordArray<A, I> {
    fn index_mut(&mut self, index: I) -> &mut Self::Output {
        &mut self.0.slice_mut()[index.into()]
    }
}
impl<A: ArrayBacking, I: Into<usize>> std::ops::Deref for WordArray<A, I> {
    type Target = [Word];

    fn deref(&self) -> &Self::Target {
        self.0.slice()
    }
}
impl<A: ArrayBacking, I: Into<usize>> std::ops::DerefMut for WordArray<A, I> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        self.0.slice_mut()
    }
}
impl<A: ArrayBacking, I> std::fmt::Debug for WordArray<A, I> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_list()
            .entries(self.0.slice())
            .finish()
    }
}