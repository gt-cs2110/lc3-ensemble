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

/// A condition code (used for BR), must be between 0 and 7.
pub type CondCode = u8;
/// A signed offset or a signed immediate value.
/// `N` indicates the maximum bit size of this offset/immediate value.
/// 
/// For example, `IOffset<5>` is equivalent to `ADD`/`AND`'s imm5 operand.
pub type IOffset<const N: usize> = Offset<i16, N>;
/// A trap vector (used for TRAP).
pub type TrapVect8 = Offset<u16, 8>;

/// Either an immediate value or a register.
/// 
/// This is used in instances like `AND`/`ADD` to handle a data value being possibly an imm5 or a register.
#[derive(Debug, PartialEq, Eq, Hash)]
pub enum ImmOrReg<const N: usize> {
    Imm(IOffset<N>),
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

/// An offset or immediate value.
/// 
/// The `OFF` type represents the backing type of this offset, 
/// and the signedness of the offset is based on the signedness of the `OFF` type.
/// 
/// For example, `Offset<i16, _>` is a signed offset, whereas `Offset<u16, _>` is an unsigned offset.
/// 
/// `N` indicates the maximum bit size of this offset/immediate value.
/// 
/// For example, `Offset<i16, 5>` is equivalent to `ADD`/`AND`'s imm5 operand.
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
    CannotFitUnsigned,
    CannotFitSigned
}
macro_rules! impl_offset {
    ($Int:ty, $ErrIdent:ident) => {
        impl<const N: usize> Offset<$Int, N> {
            /// Creates a new offset.
            /// This must fit within `N` bits of the representation, otherwise an error is raised.
            pub fn new(n: $Int) -> Result<Self, OffsetNewError> {
                match n == (n << (16 - N)) >> (16 - N) {
                    true  => Ok(Offset(n)),
                    false => Err(OffsetNewError::$ErrIdent),
                }
            }

            /// Creates a new offset by sign-extending the first N bits of the integer.
            pub fn new_trunc(n: $Int) -> Self {
                Self((n << (16 - N)) >> 16 - N)
            }
            pub fn get(&self) -> $Int {
                self.0
            }

            /// 
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
/// During the first pass, this is replaced with a regular `Offset` type.
#[derive(Debug, PartialEq, Eq, Hash)]
pub enum PCOffset<OFF, const N: usize> {
    Offset(Offset<OFF, N>),
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