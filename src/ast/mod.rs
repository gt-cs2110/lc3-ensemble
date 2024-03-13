pub mod sim;

use std::fmt::Write as _;

pub(crate) struct Reg(pub u8);
impl std::fmt::Display for Reg {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "R{}", self.0)
    }
}

type Imm5 = Offset<i16, 5>;
type CondCode = u8;
type IOffset<const N: usize> = Offset<i16, N>;
type TrapVect8 = Offset<u16, 8>;

pub(crate) enum ImmOrReg<const N: usize> {
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

pub(crate) struct Offset<OFF, const N: usize>(pub OFF);

impl<OFF: std::fmt::Display, const N: usize> std::fmt::Display for Offset<OFF, N> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_char('#')?;
        self.0.fmt(f)
    }
}
impl<const N: usize> std::fmt::Binary for Offset<u16, N> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_char('b')?;
        self.0.fmt(f)
    }
}
impl<const N: usize> std::fmt::LowerHex for Offset<u16, N> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_char('x')?;
        self.0.fmt(f)
    }
}
impl<const N: usize> std::fmt::UpperHex for Offset<u16, N> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_char('x')?;
        self.0.fmt(f)
    }
}

enum PCOffset<OFF, const N: usize> {
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

macro_rules! impl_offset {
    ($Int:ty, $sign:literal) => {
        impl<const N: usize> Offset<$Int, N> {
            fn new(n: $Int) -> Result<Self, ()> {
                match n == (n << (16 - N)) >> (16 - N) {
                    true  => Ok(Offset(n)),
                    false => Err(()),
                }
            }

            fn repr(&self) -> u16 {
                (self.0 as u16) & ((1 << N) - 1)
            }
        }
    }
}
impl_offset!(u16, "unsigned");
impl_offset!(i16, "signed");
