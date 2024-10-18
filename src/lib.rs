#![no_std]
#![cfg_attr(any(docsrs, feature = "__internal_test_docs"), allow(internal_features))]
#![cfg_attr(any(docsrs, feature = "__internal_test_docs"), feature(rustdoc_internals))]
#![forbid(unsafe_code)]


/*!
# fn_bnf

This crate contains a `no_std` compatible, low-allocation parsing library
that uses a BNF-like syntax with the [`define!`] macro to allow for
using arbitrary Rust items as grammar rules, 
and for parsing both `str`s and any `[T]` (for example, `[u8]` or `[Token]`).

TODO: Write this documentation more better

*/

use core::{marker::PhantomData, ops::{Index, RangeTo}};

extern crate alloc;
#[doc(hidden)]
pub use alloc::{boxed::Box, vec::Vec};
#[doc(hidden)]
pub use core::{error::Error, fmt::Write};

mod combinators;
pub use combinators::*;

mod def_tuple;
mod definitions;

#[derive(Default, Debug)]
/// Holds data about something that went wrong while parsing a rule.
pub struct ParseError {
    /// The underlying error that caused parsing to halt, if any.
    pub cause: Option<Box<dyn Error>>,
    /// The name of the rule that failed.
    pub rule_name: Option<&'static str>, 
    /// The slice index where the rule failed to parse.
    pub index: usize,
}

impl ParseError {
    #[must_use]
    /// Creates a new instance of a parsing error.
    pub const fn new(cause: Option<Box<dyn Error>>, rule_name: Option<&'static str>, index: usize) -> Self {
        Self { cause, rule_name, index }
    }
}

impl core::fmt::Display for ParseError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        if !f.alternate() {
            if let Some(cause) = self.cause.as_ref() {
                return write!(f, "{cause}");
            }
        }
        write!(f, "error")?;
        if let Some(name) = self.rule_name {
            write!(f, " in rule {name}")?;
        }
        write!(f, " at index {}", self.index)?;
        if let Some(cause) = self.cause.as_ref() {
            write!(f, ": {cause}")?;
        }
        Ok(())
    }
}

impl Error for ParseError {
    fn source(&self) -> Option<&(dyn Error + 'static)> {
        self.cause.as_deref()
    }
}

/// Defines a rule's name separate from the [`Rule`] trait.
/// 
/// # Why a separate trait?
/// Since [`Rule`] is bound by its slice type,
/// accessing this function would require knowing that type unambiguously.
/// 
/// However, within [`crate::define`], the macro can only call `.name()`,
/// as it doesn't know the type of the underlying rule,
/// _meaning_ that it can't resolve any ambiguity caused by a rule that's generic over multiple slice types.
/// 
/// However, as this trait doesn't include the slice type anywhere, there is no ambiguity.
pub trait NamedRule {
    /// Defines the name printed in errors including this rule.
    fn name(&self) -> Option<&'static str> { None }
}

/// Trait dictating that something can be used as a rule within a parsing grammar.
pub trait Rule<'input, SliceType: ?Sized + 'input>: NamedRule {
    /// The type of the value of a successful parse of this rule.
    type Output;

    /// Parses a rule at a given index with a given input.
    /// 
    /// # Errors
    /// Errors if the rule fails to parse.
    /// 
    /// # Correctness
    /// It is **critical** that you reset the values of `input` and `index` if an error occurs!
    /// 
    /// For example, this can be done as follows:
    /// ```ignore
    /// let before = (*input, *index);
    /// // later...
    /// let res = match inner_rule.parse_at(input, index) {
    ///     Ok(v) => v,
    ///     Err(err) => {
    ///         (*input, *index) = before;
    ///         return Err(err);
    ///     }
    /// }
    /// ```
    /// 
    /// If this is not upheld, other code using your rule may misbehave, potentially inducing panics and/or non-termination.
    /// **As this is not a safety contract, implementors cannot rely on this for soundness in `unsafe` code.** 
    fn parse_at<'cursor, 'this, 'index>(&'this self, input: &'cursor mut &'input SliceType, index: &'index mut usize)
        -> Result<Self::Output, ParseError> where 'input: 'this;
    
    /// Parses a given rule at the start of some input.
    /// 
    /// # Errors
    /// Errors if the rule fails to parse.
    fn parse<'this>(&'this self, input: &'input SliceType)
        -> Result<(&'input SliceType, Self::Output), ParseError>
        where 'input: 'this
    {
        let input = &mut &*input;
        self.parse_at(input, &mut 0)
            .map(|tree| (*input, tree))
    }

    /// Maps an infallible function onto the output of a rule.
    #[inline]
    fn map_parsed<Output, F: Fn(Self::Output) -> Output>(self, function: F) -> Map<'input, SliceType, Self, Output, F> where Self: Sized {
        Map { inner: self, func: function, _p: PhantomData }
    }

    /// Maps a function onto the output of a rule, passing the error back if it fails.
    #[inline]
    fn try_map_parsed<Output, E: Error + 'static, F: Fn(Self::Output) -> Result<Output, E>>(self, function: F) -> TryMap<'input, SliceType, Self, Output, E, F> where Self: Sized {
        TryMap { inner: self, func: function, _p: PhantomData }
    }

    /// Matches when self fails, and vice versa.
    #[inline]
    fn prevent(self) -> Not<Self> where Self: Sized {
        Not(self)
    }

    /// Repeats this rule a set amount of times.
    #[inline]
    fn repeat<const REPS: usize>(self) -> Repeat<'input, SliceType, Self, REPS> where Self: Sized {
        Repeat::<'input, SliceType, Self, REPS>(self, PhantomData)
    }

    /// Repeats this rule at most a set amount of times.
    #[inline]
    fn take(self, at_most: usize) -> Many<'input, SliceType, Self> where Self: Sized {
        Many::limited(self, at_most)
    }

    /// Repeats this rule forever until it fails.
    #[inline]
    fn hoard(self) -> Many<'input, SliceType, Self> where Self: Sized {
        Many::unlimited(self)
    }

    /// Repeats this rule until the end of input, failing if it ever does.
    #[inline]
    fn consume_all(self) -> Consume<'input, SliceType, Self> 
        where Self: Sized, 
        Consume<'input, SliceType, Self>: Rule<'input, SliceType, Output = Vec<Self::Output>>
    {
        Consume(self, PhantomData)
    }

    /// Captures the output and span of this rule, returning them along with the output in a [`Span`].
    #[inline]
    fn spanned(self) -> Spanned<'input, SliceType, Self>
        where Self: Sized, SliceType: Index<RangeTo<usize>, Output = SliceType>
    {
        Spanned { rule: self, _p: PhantomData }
    }

    /// Tries to capture this rule, returning [`None`] if it doesn't match.
    #[inline]
    fn attempt(self) -> Attempt<'input, SliceType, Self>
        where Self: Sized
    {
        Attempt(self, PhantomData)
    }
}

pub use fn_bnf_macro::*; 