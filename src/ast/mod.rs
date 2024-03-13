pub mod sim;

use std::fmt::Write as _;

/// A register. Must be between 0 and 7.
#[derive(Debug, PartialEq, Eq, Hash)]
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
pub type IOffset<const N: usize> = Offset<i16, N>;
/// An unsigned 8-bit trap vector (used for `TRAP`).
pub type TrapVect8 = Offset<u16, 8>;

/// A value representing either an immediate value or a register.
/// 
/// This is used to handle the second operand `AND`/`ADD`, which
/// can be either an immediate value or a register.
#[derive(Debug, PartialEq, Eq, Hash)]
pub enum ImmOrReg<const N: usize> {
    #[allow(missing_docs)]
    Imm(IOffset<N>),
    #[allow(missing_docs)]
    Reg(Reg)
}
impl<const N: usize> std::fmt::Display for ImmOrReg<N> {
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
#[derive(Debug, PartialEq, Eq, Hash)]
pub struct Offset<OFF, const N: usize>(OFF);

impl<OFF: std::fmt::Display, const N: usize> std::fmt::Display for Offset<OFF, N> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_char('#')?;
        self.0.fmt(f)
    }
}
impl<OFF: std::fmt::Binary, const N: usize> std::fmt::Binary for Offset<OFF, N> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_char('b')?;
        self.0.fmt(f)
    }
}
impl<OFF: std::fmt::LowerHex, const N: usize> std::fmt::LowerHex for Offset<OFF, N> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_char('x')?;
        self.0.fmt(f)
    }
}
impl<OFF: std::fmt::UpperHex, const N: usize> std::fmt::UpperHex for Offset<OFF, N> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_char('X')?;
        self.0.fmt(f)
    }
}

/// The errors that can result from calling `Offset::new`.
#[derive(Debug, PartialEq, Eq)]
pub enum OffsetNewError {
    /// The provided offset cannot fit an unsigned integer of the given bitsize.
    CannotFitUnsigned(usize),
    /// The provided offset cannot fit a signed integer of the given bitsize.
    CannotFitSigned(usize)
}
macro_rules! impl_offset {
    ($Int:ty, $ErrIdent:ident) => {
        impl<const N: usize> Offset<$Int, N> {
            /// Creates a new offset value.
            /// This must fit within `N` bits of the representation, otherwise an error is raised.
            pub fn new(n: $Int) -> Result<Self, OffsetNewError> {
                match n == (n << (16 - N)) >> (16 - N) {
                    true  => Ok(Offset(n)),
                    false => Err(OffsetNewError::$ErrIdent(N)),
                }
            }

            /// Creates a new offset by sign-extending the first N bits of the integer.
            pub fn new_trunc(n: $Int) -> Self {
                Self((n << (16 - N)) >> 16 - N)
            }

            /// Gets the value of the offset.
            pub fn get(&self) -> $Int {
                self.0
            }

            /// Gets the representation of the value, setting any excess bits to 0.
            pub fn repr(&self) -> u16 {
                (self.0 as u16) & ((1 << N) - 1)
            }
        }
    }
}
impl_offset!(u16, CannotFitUnsigned);
impl_offset!(i16, CannotFitSigned);

/// An offset or a label.
/// 
/// This is used to represent PCOffset operands 
/// (such as PCOffset9 in `LD` and `ST` and PCOffset11 in `JSR`).
/// 
/// During the first assembly pass, the label is resolved and
/// replaced with a regular [`Offset`] value.
/// 
/// [`Offset`]: Offset
#[derive(Debug, PartialEq, Eq, Hash)]
pub enum PCOffset<OFF, const N: usize> {
    #[allow(missing_docs)]
    Offset(Offset<OFF, N>),
    #[allow(missing_docs)]
    Label(String)
}
impl<OFF, const N: usize> std::fmt::Display for PCOffset<OFF, N> 
    where Offset<OFF, N>: std::fmt::Display
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            PCOffset::Offset(off)  => off.fmt(f),
            PCOffset::Label(label) => label.fmt(f),
        }
    }
}