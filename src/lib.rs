#![no_std]
#![cfg_attr(any(docsrs, feature = "__internal_test_docs"), allow(internal_features))]
#![cfg_attr(any(docsrs, feature = "__internal_test_docs"), feature(rustdoc_internals))]
#![forbid(unsafe_code)]
#![cfg_attr(feature = "error_in_core", feature(error_in_core))]

/*!

[![Repository](https://img.shields.io/badge/-GitHub-%23181717?style=flat&logo=github&labelColor=%23555555&color=%23181717)](https://github.com/balt-dev/fn-bnf)
[![Latest version](https://img.shields.io/crates/v/fn-bnf.svg)](
https://crates.io/crates/fn-bnf)
[![Documentation](https://docs.rs/fn-bnf/badge.svg)](
https://docs.rs/fn-bnf)
[![MSRV](https://img.shields.io/badge/MSRV-1.81.0-red)](
https://gist.github.com/alexheretic/d1e98d8433b602e57f5d0a9637927e0c)
[![unsafe forbidden](https://img.shields.io/badge/unsafe-forbidden-success.svg)](
https://github.com/rust-secure-code/safety-dance/)
[![License](https://img.shields.io/crates/l/fn-bnf.svg)](
https://github.com/balt-dev/fn-bnf/blob/master/LICENSE-MIT)

# fn-bnf

This crate contains a `no_std` compatible, low-allocation parsing library
that uses a BNF-like syntax with the [`define!`] macro to allow for
using arbitrary Rust items as grammar rules, 
and for parsing both `str`s and any `[T]` (for example, `[u8]` or `[Token]`).

If you just want to skip to writing grammars, look at the documentation for [`define!`]. 

# Feature flags

This crate has two feature flags:
- `more_tuple_impls`, raising the amount of elements [`Rule`] is implemented for
on tuples of [`Rule`]s from 16 to 256 - however, enabling this will raise compilation times dramatically
- `error_in_core`, enabling use of this library before Rust 1.81.0 on `nightly` compilers - 
  however, continued support for versions below 1.81.0 is not guaranteed

# A note about the stack

This library's very lifeblood is deep - and likely recursive - function calls.
You may run into stack overflow issues if you have an overly complex grammar, or are blindly parsing malicious input.

# Licensing

This crate is dual-licensed under the Apache 2.0 or MIT licenses.
*/

extern crate self as fn_bnf;

use core::{marker::PhantomData, ops::{Index, RangeTo}};

extern crate alloc;
#[doc(hidden)]
pub use alloc::{boxed::Box, vec::Vec};
#[doc(hidden)]
pub use core::{error::Error, fmt::Write};

mod rules;
pub use rules::*;

/// Contains some common error types.
pub mod errors {
    crate::err! {
        pub UnmatchedInput: "expected input to match function",
        pub UnexpectedMatch: "matched input unexpectedly",
        pub UnexpectedEOF: "unexpected end of input",
        pub ExhaustedInput: "no options matched for rule",
        pub NoMatch: "could not match literal"
    }

    /// A canonical error for when a grammar simply finds something it doesn't expect.
    #[derive(Debug, Copy, Clone)]
    pub struct Unexpected<T: core::fmt::Debug> { val: T }
    impl<T: core::fmt::Debug> Unexpected<T> {
        /// Creates a new instance of this type.
        #[inline]
        pub const fn new(val: T) -> Self {
            Self { val }
        }
    }

    impl<T: core::fmt::Debug> core::fmt::Display for Unexpected<T> {
        fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
            write!(f, "unexpected token: {:?}", self.val)
        }
    }

    impl<T: core::fmt::Debug> core::error::Error for Unexpected<T> {}
}
use errors::*;

mod def_tuple;
mod definitions;

#[derive(Default, Debug)]
/// Holds data about something that went wrong while parsing a rule.
pub struct ParseError {
    /// The underlying error that caused parsing to halt, if any.
    /// 
    /// Note that for ZST [`Error`] implementations, like those created by [`crate::err!`],
    /// `Box<dyn Error>` doesn't allocate.
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
/// Most of the time, the [derive macro](fn_bnf_macro::NamedRule) works well enough for this purpose.
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
/// 
/// # Implementation
/// Imlpementing this trait means that anyone can use your struct as a rule
/// in any of their their grammars with a supported slice type.
/// 
/// If you're defining simple rules that don't depend on the input,
/// you _can_ make rules generic over all slice types!
/// 
/// This is done for most of the "helper rules", like [`Any`], in this crate.
pub trait Rule<'input, SliceType: ?Sized + 'input>: NamedRule {
    /// The type of the value of a successful parse of this rule.
    type Output;

    /// Parses a rule at a given index with a given input.
    /// 
    /// # Errors
    /// Errors if the rule fails to parse.
    /// 
    /// # Correctness
    /// When a parse succeeds, you must replace the borrowed input and index
    /// with a slice of it past the index you stopped parsing at - for example,
    /// ```ignore
    /// *input = &input[2..];
    /// *index += 2;
    /// ```
    /// 
    /// You also must reset the values of `input` and `index` if an error occurs.
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
    /// Fsilure to do uphold of these could cause other code using your rule to misbehave,
    /// potentially inducing panics and/or non-termination.
    /// 
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

    /// Matches when this fails, and vice versa.
    #[inline]
    fn prevent(self) -> Not<Self> where Self: Sized {
        Not(self)
    }

    /// Repeats this rule a known amount of times.
    #[inline]
    fn repeat_for<const REPS: usize>(self) -> RepeatFor<'input, SliceType, Self, REPS> where Self: Sized {
        RepeatFor::<'input, SliceType, Self, REPS>(self, PhantomData)
    }

    /// Repeats this rule a set amount of times.
    #[inline]
    fn repeat(self, reps: usize) -> Repeat<'input, SliceType, Self> where Self: Sized {
        Repeat::<'input, SliceType, Self>(self, reps, PhantomData)
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

/// Derive macro generating an impl of the trait `NamedRule`.
pub use fn_bnf_macro::NamedRule;

// TO EXPLAIN:
//     The basic syntax
//     'input and arg_#
//     AnyRule
//     Also, linkhere to [`Rule`] and explain there how to impl manually!

/// Allows defining multiple custom rules using a PEG-like syntax.
/// 
/// # Syntax and explanation
/// 
/// First, we have the name, visibility, and "slice type" of the grammar:
/// ```ignore
/// pub grammar Name<Type>
/// ```
/// The visibility and name are self-explanatory, 
/// and the "slice type" determines what type this grammar parses.
/// 
/// If you want to parse a string, you can use `str` as your slice type,
/// or if you want to parse bytes, you create a grammar with type `[u8]`.
/// 
/// Note that the type inside a `[T]` can be just about anything, so this works fine:
/// ```ignore
/// enum Token { LParen, RParen, Number(f64), Plus, Minus, Asterisk, Slash }
/// define! {
///     pub grammar Expression<[Token]> { /* ... */ }
/// }
/// ```
/// However, due to limitations caused by trait implementation collisions[^1], 
/// you can't use a `T` as a rule for a `[T]` grammar -
/// you have to use a 1-long array.
/// 
/// Moving on, we come to defining individual rules,
/// which is better described with a few examples:
/// 
/// ```ignore
/// /// Parses either `Tap`, `Tag`, or `Box`.
/// Sample -> (&'input str, Option<char>) = "Ta", ('p', 'g') : "Box";
/// ```
/// 
/// We see here the basic syntax of defining a rule:
/// - Any attributes/documentation
/// - The rule's name
/// - The rule's return type
/// - `=`
/// - A `:` separated list of potential ways to parse the rule (we call these "parsing paths"),
///   where each option is a list of `,` separated [`Rule`]s.
/// 
/// A rule's return type is a tuple with arity determined by its options.
/// If two different paths have different arity, then
/// any return types past the minimum amount between all options
/// will be wrapped in an [`Option`], returning `None` for rules which don't have them.
/// 
/// For example, this:
/// ```ignore
/// A -> (char, Option<char>) = 'b', 'c' : 'd';
/// ```
/// will return `('b', Some('c'))` for `"bc"`, but `("d", None)` for `"d"`.
/// 
/// Paths are parsed sequentially, so in the above example, 
/// 
/// As a special case, a rule with arity 1 will return its inner type instead of a 1-tuple,
/// and a rule with arity 0 will return `()`.
/// 
/// Let's look at a more complicated example:
/// ```ignore
/// /// Parses an unsigned  number, potentially surrounded by parentheses.
/// pub ParenNumber -> u32 = _ '(', ParenNumber, _ ')' : Number;
/// /// Parses an unsigned number.
/// Number -> u32 try_from(u32::from_str) = While::from(char::is_ascii_digit);
/// ```
/// 
/// Here, we see a few things.
/// 
/// Firstly, rules support arbitrary documentation and attributes,
/// all of which will be applied to the generated `struct`.
/// 
/// Second, there's support for a visibility in front of a rule - 
/// a rule must be `pub` (or `pub(super)`, or `pub(crate)`, etc.)
/// to be accessible outside of the grammar's definition.
/// 
/// After that, we see some new syntax in the form of `_`.
/// Prefixing any part of a path with an underscore makes the grammar
/// not store its output, and not save it as an argument.
/// 
/// Finally, we see `try_from`.
/// This, along with its infallible counterpart `from`,
/// takes the output of your entire rule and passes it into a given function.
/// 
/// This function will need to take the amount and type of arguments 
/// equal to the arity and elements of the tuple it would usually output -
/// in layman's terms, the tuple is "unpacked" into the function, similar to `...` in JavaScript or `*` in Python.
/// 
/// A function given to `from` must return the type of the rule, 
/// and a function given to `try_from` must return a `Result<T, E>`,
/// where T is the type of the rule, and `E` is any type that implements [`Error`]. 
/// 
/// We also see that rules can _recurse_ - although this should be avoided if reasonably possible.
/// If a rule recurses too deep, then Rust's call stack will be exhausted and your program will crash!
/// If you truly need deep recursion, look into crates like [`stacker`](https://docs.rs/stacker/).
/// 
/// Finally, let's look at an advanced example:
/// ```ignore
/// pub Doubled<'input, R> {rule: R, _p: PhantomData<&'input str>} -> &'input str
///     where R: Rule<'input, str, Output = &'input str>
///     = &self.rule, _ arg_0;
/// ```
/// 
/// We see here that rules are simply structs, and can take generics and fields as such.
/// 
/// Also to note is the usage of `arg_0`.
/// Previously parsed arguments (ignoring silenced ones) are left in scope as `arg_N`,
/// where N is the index of the argument.
/// 
/// Importantly, `'input` is special - it's always in scope, even if not declared,
/// and is the lifetime of the data that's being passed in.
/// 
/// Anything that implements `for<'input> Rule<'input, T>`
/// will work in _any_ grammar of slice type `T` - 
/// they don't have to even be from the same macro!
/// 
/// For example, this is fine:
/// ```ignore
/// define! {
///     grammar Theta<str> {
///         pub Foo -> &'input str = "foo"; 
///     }
/// }
///
/// define! {
///     grammar Delta<str> {
///         pub Bar -> &'input str = Theta::Foo;
///     }
/// }
/// ```
/// 
/// Alternatively, if, <sub>God forbid, </sub>something happens so that you need to implement a [`Rule`] manually, 
/// without the help of this macro, look at the documentation for that trait - it'll tell you everything you need to know.
/// 
/// # Example
/// Below is the entire source code for `examples/math.rs`, showing a simple CLI calculator app.
/// ```rust
#[doc = include_str!("../examples/math.rs")]
/// ```
/// 
/// [^1]: It's ambiguous between `[T]` and `[&T]`, and between `[T]` and `[(T, )]`.
///       Ideally, the library could `impl !Rule` for these, but even disregarding
///       the fact that that's nightly, it doesn't work - at least, for now.
///       Said bounds would be equivalent to [specialization](https://github.com/rust-lang/rust/issues/31844),
///       which is a long way off.
pub use fn_bnf_macro::define;

// Reimplementing never_say_never because it has documentation that messes with ours
// never_say_never is under the MIT license, among others: 
// https://github.com/danielhenrymantilla/never-say-never.rs/blob/master/LICENSE-MIT
mod fn_trait {
    pub trait FnOnce<Args> { type Output; }
    impl<F, R> FnOnce<()> for F where F: core::ops::FnOnce() -> R { type Output = R; }
}
use fn_trait::FnOnce;

/// The [`!`] type.
/// 
/// This type is (meant to be) unstable, but it's much more useful than
/// [`core::convert::Infallible`] for writing grammars due to its coercion rules,
/// so it is exported here.
/// 
pub type Never = <fn() -> ! as FnOnce<()>>::Output;
