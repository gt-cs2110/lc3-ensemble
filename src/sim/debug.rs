//! Utilities to debug simulation.
//! 
//! The key type here is [`Breakpoint`], which can be appended to the [`Simulator`]'s
//! breakpoint field to cause the simulator to break.
use std::fmt::Write;
use std::sync::Mutex;

use crate::ast::Reg;

use super::Simulator;

macro_rules! fmt_cmp {
    ($f:expr, $cmp:expr) => { fmt_cmp!($f, $cmp, "{}") };
    ($f:expr, $cmp:expr, $lit:literal) => {
        match $cmp.flag {
            0b000 => write!($f, "never"),
            0b100 => write!($f, concat!("< ", $lit), $cmp.value),
            0b010 => write!($f, concat!("== ", $lit), $cmp.value),
            0b110 => write!($f, concat!("<= ", $lit), $cmp.value),
            0b001 => write!($f, concat!("> ", $lit), $cmp.value),
            0b101 => write!($f, concat!("!= ", $lit), $cmp.value),
            0b011 => write!($f, concat!(">= ", $lit), $cmp.value),
            0b111 => write!($f, "always"),
            _ => unreachable!("comparator flag should have been less than 8")
        }
    }
}

/// Common breakpoints.
pub enum Breakpoint {
    /// Break when the PC is equal to the given value.
    PC(Comparator),

    /// Break when the provided register is set to a given value.
    Reg {
        /// Register to check.
        reg: Reg,
        /// Predicate to break against.
        value: Comparator
    },
    /// Break when the provided memory address is written to with a given value.
    Mem {
        /// Address to check.
        addr: u16,
        /// Predicate to break against.
        value: Comparator
    },

    /// Breaks based on an arbitrarily defined function.
    /// 
    /// This can be constructed with the [`Breakpoint::generic`] function.
    Generic(BreakpointFn),

    /// Both conditions have to apply for the break to be applied.
    And([Box<Breakpoint>; 2]),
    /// One of these conditions have to apply for the break to be applied.
    Or([Box<Breakpoint>; 2]),
}

impl Breakpoint where Breakpoint: Send + Sync { /* assert Breakpoint is send/sync */ }
type BreakpointFn = Mutex<Box<dyn FnMut(&Simulator) -> bool + Send + 'static>>;

impl Breakpoint {
    /// Creates a breakpoint out of a function.
    pub fn generic(f: impl FnMut(&Simulator) -> bool + Send + 'static) -> Breakpoint {
        Breakpoint::Generic(Mutex::new(Box::new(f)))
    }

    /// Checks if a break should occur.
    pub fn check(&self, sim: &Simulator) -> bool {
        match self {
            Breakpoint::PC(cmp) => cmp.check(sim.pc),
            Breakpoint::Reg { reg, value: cmp } => cmp.check(sim.reg_file[*reg].get()),
            Breakpoint::Mem { addr, value: cmp } => cmp.check(sim.mem.0[*addr as usize].get()), // this is not using mem's get because we don't want to trigger an IO read
            Breakpoint::Generic(pred) => (pred.lock().unwrap())(sim),
            Breakpoint::And([l, r]) => l.check(sim) && r.check(sim),
            Breakpoint::Or([l, r]) => l.check(sim) || r.check(sim),
        }
    }

    fn fmt_bp(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        match self {
            Self::PC(cmp) => {
                f.write_str("PC ")?;
                fmt_cmp!(f, cmp, "x{:04X}")?;
            },
            Self::Reg { reg, value } => {
                write!(f, "{reg} ")?;
                fmt_cmp!(f, value)?;
            },
            Self::Mem { addr, value } => {
                write!(f, "mem[x{addr:04X}] ")?;
                fmt_cmp!(f, value)?;
            },
            Self::Generic(_) => f.debug_struct("Generic").finish_non_exhaustive()?,
            Self::And([l, r]) => {
                f.write_char('(')?;
                l.fmt_bp(f)?;
                f.write_str(") && (")?;
                r.fmt_bp(f)?;
                f.write_char(')')?;
            },
            Self::Or([l, r]) => {
                f.write_char('(')?;
                l.fmt_bp(f)?;
                f.write_str(") || (")?;
                r.fmt_bp(f)?;
                f.write_char(')')?;
            },
        }
        Ok(())
    }
}
impl std::fmt::Debug for Breakpoint {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str("Breakpoint(")?;
        self.fmt_bp(f)?;
        f.write_char(')')
    }
}
impl std::ops::BitAnd for Breakpoint {
    type Output = Breakpoint;

    fn bitand(self, rhs: Self) -> Self::Output {
        Breakpoint::And([Box::new(self), Box::new(rhs)])
    }
}
impl std::ops::BitOr for Breakpoint {
    type Output = Breakpoint;

    fn bitor(self, rhs: Self) -> Self::Output {
        Breakpoint::Or([Box::new(self), Box::new(rhs)])
    }
}

/// Predicate checking whether the current value is equal to the value.
pub struct Comparator {
    flag: u8,
    /// The value we're checking against.
    pub value: u16
}
impl Comparator {
    /// Never breaks.
    pub fn never() -> Self {
        Self { flag: 0b000, value: 0 }
    }
    /// Break if the desired value is less than the provided value.
    pub fn lt(value: u16) -> Self {
        Self { flag: 0b100, value }
    }
    /// Break if the desired value is equal to the provided value.
    pub fn eq(value: u16) -> Self {
        Self { flag: 0b010, value }
    }
    /// Break if the desired value is less than or equal to the provided value.
    pub fn le(value: u16) -> Self {
        Self { flag: 0b110, value }
    }
    /// Break if the desired value is greater than the provided value.
    pub fn gt(value: u16) -> Self {
        Self { flag: 0b001, value }
    }
    /// Break if the desired value is not equal to the provided value.
    pub fn ne(value: u16) -> Self {
        Self { flag: 0b101, value }
    }
    /// Break if the desired value is greater than or equal to the provided value.
    pub fn ge(value: u16) -> Self {
        Self { flag: 0b011, value }
    }
    /// Always breaks.
    pub fn always() -> Self {
        Self { flag: 0b111, value: 0 }
    }

    /// Checks if the operand passes the comparator.
    pub fn check(&self, operand: u16) -> bool {
        let cmp_flags = match operand.cmp(&self.value) {
            std::cmp::Ordering::Less    => 0b100,
            std::cmp::Ordering::Equal   => 0b010,
            std::cmp::Ordering::Greater => 0b001,
        };

        (cmp_flags & self.flag) != 0
    }
}

#[cfg(test)]
mod test {
    use crate::ast::reg_consts::R7;
    use crate::sim::debug::{Breakpoint, Comparator};

    #[test]
    fn print() {
        println!("{:?}", Breakpoint::Reg { reg: R7, value: Comparator::lt(14) } & Breakpoint::Reg { reg: R7, value: Comparator::ge(10) });
        println!("{:?}", Breakpoint::Mem { addr: 0x4000, value: Comparator::lt(14) } | Breakpoint::Mem { addr: 0x5000, value: Comparator::ge(10) } & Breakpoint::PC(Comparator::eq(0x3000)));
    }
}