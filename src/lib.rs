#![no_std]
#![cfg_attr(any(docsrs, feature = "__internal_test_docs"), allow(internal_features))]
#![cfg_attr(any(docsrs, feature = "__internal_test_docs"), feature(rustdoc_internals))]

use core::{marker::PhantomData, ops::{Index, RangeTo}};

mod shims;
use shims::*;

mod combinators;
pub use combinators::*;

mod def_tuple;
mod definitions;

#[doc(hidden)]
pub use shims::Box;
#[doc(hidden)]
#[inline]
pub const fn get_name_string<'input, T: ?Sized + 'input, R: Rule<'input, T>>(_val: &R) -> Option<&'static str> {
    R::NAME
}

#[derive(Default, Debug)]
pub struct ParseError {
    pub cause: Option<Box<dyn Error>>,
    pub rule_name: Option<&'static str>, 
    pub index: usize,
}

impl ParseError {
    pub const fn new(cause: Option<Box<dyn Error>>, rule_name: Option<&'static str>, index: usize) -> Self {
        Self { cause, rule_name, index }
    }
}

impl core::fmt::Display for ParseError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
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
        self.cause.as_ref().map(|v| &**v)
    }
}

pub trait Rule<'input, SliceType: ?Sized + 'input> {
    const NAME: Option<&'static str> = None;
    type Output;

    /// Parses a rule at a given index with a given input.
    /// 
    /// # Errors
    /// Errors if the rule fails to parse.
    /// 
    /// # Implementor's note
    /// If you are implementing this method, 
    /// it is **very important** that you reset the values of `input` and `index` if an error occurs!
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
    fn parse_at<'cursor, 'this, 'index>(&'this self, input: &'cursor mut &'input SliceType, index: &'index mut usize)
        -> Result<Self::Output, ParseError> where 'input: 'this;
    
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
    fn map_parsed<Output>(self, function: impl Fn(Self::Output) -> Output) -> impl Rule<'input, SliceType, Output = Output> where Self: Sized {
        Map { inner: self, func: function, _p: PhantomData }
    }

    /// Maps a function onto the output of a rule, passing the error back if it fails.
    #[inline]
    fn try_map_parsed<Output, E: Error + 'static>(self, function: impl Fn(Self::Output) -> Result<Output, E>) -> impl Rule<'input, SliceType, Output = Output> where Self: Sized {
        TryMap { inner: self, func: function, _p: PhantomData }
    }

    /// Matches when self fails, and vice versa.
    #[inline]
    fn prevent(self) -> impl Rule<'input, SliceType, Output = ()> where Self: Sized {
        Not(self)
    }

    /// Repeats this rule a set amount of times.
    #[inline]
    fn repeat<const REPS: usize>(self) -> impl Rule<'input, SliceType, Output = [Self::Output; REPS]> where Self: Sized {
        Repeat::<Self, REPS>(self)
    }

    /// Repeats this rule at most a set amount of times.
    #[inline]
    fn take(self, at_most: usize) -> impl Rule<'input, SliceType, Output = Vec<Self::Output>> where Self: Sized {
        Many::limited(self, at_most)
    }

    /// Repeats this rule forever until it fails.
    #[inline]
    fn hoard(self) -> impl Rule<'input, SliceType, Output = Vec<Self::Output>> where Self: Sized {
        Many::unlimited(self)
    }

    /// Repeats this rule until the end of input, failing if it ever does.
    #[inline]
    #[allow(private_bounds)] // shh <3
    fn consume_all(self) -> impl Rule<'input, SliceType, Output = Vec<Self::Output>> where Self: Sized, Consume<Self>: Rule<'input, SliceType, Output = Vec<Self::Output>> {
        Consume(self)
    }

    /// Captures the output and span of this rule, returning them along with the output in a [`Span`].
    #[inline]
    fn spanned(self) -> impl Rule<'input, SliceType, Output = Span<'input, SliceType, Self::Output>> 
        where Self: Sized, SliceType: Index<RangeTo<usize>, Output = SliceType>
    {
        Spanned { rule: self }
    }

    /// Tries to capture this rule, returning [`None`] if it doesn't match.
    #[inline]
    fn maybe(self) -> impl Rule<'input, SliceType, Output = Option<Self::Output>> 
        where Self: Sized
    {
        Maybe(self)
    }
}

pub use fn_bnf_macro::*; 
