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
    fn span(&self) -> Option<crate::err::ErrSpan> {
        None
    }

    /// A clarifying message to help aid someone in how to fix the message.
    /// 
    /// If there is none to add, this can be set to `None`.
    fn help(&self) -> Option<Cow<str>>;
}

/// A value that has an associated span.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Spanned<K> {
    /// The value with a span.
    pub value: K,

    /// The span in the source associated with this value.
    pub span: ErrSpan
}
impl<K> Spanned<K> {
    pub fn new<R: Into<ErrSpan>>(value: K, span: R) -> Self {
        Spanned { value, span: span.into() }
    }
}
impl<K: std::fmt::Display> std::fmt::Display for Spanned<K> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.value.fmt(f)
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum ErrSpan {
    Range(Range<usize>),
    ManyRange(Vec<Range<usize>>)
}
impl ErrSpan {
    pub fn first(&self) -> &Range<usize> {
        match self {
            ErrSpan::Range(r) => r,
            ErrSpan::ManyRange(mr) => mr.first().unwrap(),
        }
    }
    pub fn iter(&self) -> impl Iterator<Item=&Range<usize>> {
        match self {
            ErrSpan::Range(r) => std::slice::from_ref(r).iter(),
            ErrSpan::ManyRange(mr) => mr.iter(),
        }
    }
}
impl Extend<Range<usize>> for ErrSpan {
    fn extend<T: IntoIterator<Item = Range<usize>>>(&mut self, iter: T) {
        match self {
            ErrSpan::Range(r) => {
                let mut mr = vec![std::mem::replace(r, 0..0)];
                mr.extend(iter);
                *self = ErrSpan::ManyRange(mr);
            },
            ErrSpan::ManyRange(mr) => mr.extend(iter),
        }
    }
}
impl From<Range<usize>> for ErrSpan {
    fn from(value: Range<usize>) -> Self {
        ErrSpan::Range(value)
    }
}
impl From<Vec<Range<usize>>> for ErrSpan {
    fn from(value: Vec<Range<usize>>) -> Self {
        ErrSpan::ManyRange(value)
    }
}
impl From<Vec<ErrSpan>> for ErrSpan {
    fn from(value: Vec<ErrSpan>) -> Self {
        let mr = value.into_iter()
            .flat_map(|r| match r {
                ErrSpan::Range(r) => vec![r],
                ErrSpan::ManyRange(r) => r,
            })
            .collect();

        ErrSpan::ManyRange(mr)
    }
}