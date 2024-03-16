//! Structs relating to the ASTs created from assembly files.

pub mod sim;

use std::fmt::Write as _;
use offset_base::OffsetBacking;

/// A register. Must be between 0 and 7.
#[derive(Debug, PartialEq, Eq, Hash, Clone, Copy)]
pub struct Reg(pub(crate) u8);
impl std::fmt::Display for Reg {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "R{}", self.0)
    }
}

/// A condition code (used for `BR`), must be between 0 and 7.
pub type CondCode = u8;

/// A value representing a signed offset or a signed immediate value.
/// 
/// `N` indicates the maximum bit size of this offset/immediate value.
/// 
/// For example, `IOffset<5>` is used to represent `ADD`/`AND`'s imm5 operand.
pub type IOffset<const N: u32> = Offset<i16, N>;
/// An unsigned 8-bit trap vector (used for `TRAP`).
pub type TrapVect8 = Offset<u16, 8>;

/// A value representing either an immediate value or a register.
/// 
/// This is used to handle the second operand `AND`/`ADD`, which
/// can be either an immediate value or a register.
#[derive(Debug, PartialEq, Eq, Hash, Clone, Copy)]
pub enum ImmOrReg<const N: u32> {
    #[allow(missing_docs)]
    Imm(IOffset<N>),
    #[allow(missing_docs)]
    Reg(Reg)
}
impl<const N: u32> std::fmt::Display for ImmOrReg<N> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ImmOrReg::Imm(imm) => imm.fmt(f),
            ImmOrReg::Reg(reg) => reg.fmt(f),
        }
    }
}

/// A value representing an offset or an immediate value.
/// 
/// The `OFF` type represents the backing type of this offset. 
/// The signedness of this offset type is dependent on the signedness of the `OFF` type:
/// - `Offset<i16, _>`: signed offset
/// - `Offset<u16, _>`: unsigned offset
/// 
/// `N` indicates the maximum bit size of this offset/immediate value.
/// 
/// For example, `Offset<i16, 5>` is used to represent `ADD`/`AND`'s imm5 operand.
#[derive(Debug, PartialEq, Eq, Hash, Clone, Copy)]
pub struct Offset<OFF, const N: u32>(OFF);

impl<OFF: std::fmt::Display, const N: u32> std::fmt::Display for Offset<OFF, N> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_char('#')?;
        self.0.fmt(f)
    }
}
impl<OFF: std::fmt::Binary, const N: u32> std::fmt::Binary for Offset<OFF, N> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_char('b')?;
        self.0.fmt(f)
    }
}
impl<OFF: std::fmt::LowerHex, const N: u32> std::fmt::LowerHex for Offset<OFF, N> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_char('x')?;
        self.0.fmt(f)
    }
}
impl<OFF: std::fmt::UpperHex, const N: u32> std::fmt::UpperHex for Offset<OFF, N> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_char('X')?;
        self.0.fmt(f)
    }
}

/// The errors that can result from calling `Offset::new`.
#[derive(Debug, PartialEq, Eq)]
pub enum OffsetNewError {
    /// The provided offset cannot fit an unsigned integer of the given bitsize.
    CannotFitUnsigned(u32),
    /// The provided offset cannot fit a signed integer of the given bitsize.
    CannotFitSigned(u32)
}
impl std::fmt::Display for OffsetNewError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            OffsetNewError::CannotFitUnsigned(n) => write!(f, "value is too big for unsigned {n}-bit integer"),
            OffsetNewError::CannotFitSigned(n) => write!(f, "value is too big for signed {n}-bit integer"),
        }
    }
}

mod offset_base {
    use super::OffsetNewError;

    /// Any type that could store a value for [`Offset`].
    /// 
    /// [`Offset`]: super::Offset
    pub trait OffsetBacking: Copy + Eq {
        /// How many bits are contained within this backing.
        /// 
        /// For example, `u16` has 16 bits and thus BITS == 16.
        const BITS: u32;

        /// Truncates the given value to the provided `bit_size`.
        /// 
        /// This bit size is always known to be less than BITS.
        fn truncate(self, bit_size: u32) -> Self;

        /// The error to raise if a given value doesn't match
        /// its provided value when truncated to a given `bit_size`.
        fn does_not_fit_error(bit_size: u32) -> OffsetNewError;
    }
    
    macro_rules! impl_offset_backing_for_ints {
        ($($Int:ty: $Err:ident),*) => {
            $(
                impl OffsetBacking for $Int {
                    const BITS: u32 = Self::BITS;
                
                    fn truncate(self, bit_size: u32) -> Self {
                        (self << (Self::BITS - bit_size)) >> (Self::BITS - bit_size)
                    }

                    fn does_not_fit_error(bit_size: u32) -> OffsetNewError {
                        OffsetNewError::$Err(bit_size)
                    }
                }
            )*
        }
    }
    impl_offset_backing_for_ints! {
        u16: CannotFitUnsigned,
        i16: CannotFitSigned
    }
}

impl<OFF: OffsetBacking, const N: u32> Offset<OFF, N> {
    /// Creates a new offset value.
    /// This must fit within `N` bits of the representation, otherwise an error is raised.
    /// 
    /// # Panics
    /// 
    /// This will panic if `N` is larger than the offset backing (e.g., for backing `u16`, larger than 16).
    pub fn new(n: OFF) -> Result<Self, OffsetNewError> {
        assert!(N <= OFF::BITS, "bit size {N} exceeds size of backing ({})", OFF::BITS);
        match n == n.truncate(N) {
            true  => Ok(Offset(n)),
            false => Err(OFF::does_not_fit_error(N)),
        }
    }

    /// Creates a new offset by extending the first N bits of the integer,
    /// and discarding the rest.
    /// 
    /// The extension is considered sign-extended if the offset's backing is signed,
    /// and it is considered zero-extended if the offset's backing is unsigned.
    /// 
    /// # Panics
    /// 
    /// This will panic if `N` is larger than the offset backing (e.g., for backing `u16`, larger than 16).
    pub fn new_trunc(n: OFF) -> Self {
        assert!(N <= OFF::BITS, "bit size {N} exceeds size of backing ({})", OFF::BITS);
        Self(n.truncate(N))
    }

    /// Gets the value of the offset.
    pub fn get(&self) -> OFF {
        self.0
    }
}

/// An offset or a label.
/// 
/// This is used to represent [`PCOffset`] operands 
/// (such as the PCOffset9 operand in `LD` and `ST` 
/// and the PCOffset11 operand in `JSR`).
/// 
/// During the first assembly pass, the label is resolved and
/// replaced with a regular [`Offset`] value.
/// 
/// [`Offset`]: Offset
#[derive(Debug, PartialEq, Eq, Hash, Clone)]
pub enum PCOffset<OFF, const N: u32> {
    #[allow(missing_docs)]
    Offset(Offset<OFF, N>),
    #[allow(missing_docs)]
    Label(String)
}
impl<OFF, const N: u32> std::fmt::Display for PCOffset<OFF, N> 
    where Offset<OFF, N>: std::fmt::Display
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            PCOffset::Offset(off)  => off.fmt(f),
            PCOffset::Label(label) => label.fmt(f),
        }
    }
}