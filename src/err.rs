//! Error interfaces for this crate.

use std::borrow::Cow;
use std::ops::Range;

pub use crate::asm::AsmErr;
pub use crate::ast::OffsetNewErr;
pub use crate::parse::lex::LexErr;
pub use crate::parse::ParseErr;
pub use crate::sim::SimErr;

/// Unified error interface for all errors in this crate.
/// 
/// Note that the [`Display`] implementation is used for a brief message,
/// where as [`Error::help`] is used for any clarifying messages.
/// 
/// [`Display`]: std::fmt::Display
pub trait Error: std::error::Error {
    /// The range where this error occurs in source.
    /// 
    /// If this is not known, this can be set to `None`.
    fn span(&self) -> Option<Range<usize>> {
        None
    }

    /// A clarifying message to help aid someone in how to fix the message.
    /// 
    /// If there is none to add, this can be set to `None`.
    fn help(&self) -> Option<Cow<str>>;
}