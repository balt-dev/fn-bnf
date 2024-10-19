use core::ops::{Index, Range, RangeTo};

#[allow(clippy::wildcard_imports)]
use super::*;

#[macro_export]
/// Convenience macro for quickly defining errors with static messages for use in your grammars.
/// 
/// # Usage
/// ```ignore
/// err! {
///     pub InvalidFloat: "floating point literals must have an integer part",
///     pub(crate) InternalError: "internal error (this is a bug, please report)"
/// }
/// ```
macro_rules! err {
    ($($vis: vis $name: ident: $message: literal),*$(,)?) => {$(
        #[derive(Debug, Copy, Clone, Default)]
        #[doc = $message]
        $vis struct $name;
        impl ::core::fmt::Display for $name {
            fn fmt(&self, f: &mut ::core::fmt::Formatter<'_>) -> ::core::fmt::Result {
                write!(f, $message)
            }
        }
        impl ::core::error::Error for $name {}
    )*};
}

/// Maps a function over the output of a rule. See [`Rule::map_parsed`].
#[derive(Debug, Clone, PartialEq, NamedRule)]
pub struct Map<
    'input, SliceType: ?Sized, 
    R: Rule<'input, SliceType>, O, 
    Func: Fn(R::Output) -> O
> {
    pub(crate) inner: R,
    pub(crate) func: Func,
    pub(crate) _p: PhantomData<(&'input SliceType, O)>
}
impl<
    'input, SliceType: ?Sized, 
    R: Rule<'input, SliceType>, O, 
    Func: Fn(R::Output) -> O
> Rule<'input, SliceType> for Map<'input, SliceType, R, O, Func> {
    type Output = Func::Output;

    fn parse_at<'cursor, 'this, 'index>(&'this self, input: &'cursor mut &'input SliceType, index: &'index mut usize)
        -> Result<Self::Output, ParseError> where 'input: 'this 
    {
        self.inner.parse_at(input, index)
            .map(&self.func)
    }
}


/// Attempts to map a function over the output of a rule. See [`Rule::try_map_parsed`].
#[derive(Debug, Clone, PartialEq, NamedRule)]
pub struct TryMap<
    'input, SliceType: ?Sized, 
    R: Rule<'input, SliceType>, O, E: Error + 'static,
    Func: Fn(R::Output) -> Result<O, E>
> {
    pub(crate) inner: R,
    pub(crate) func: Func,
    pub(crate) _p: PhantomData<(&'input SliceType, O)>
}
impl<
    'input, SliceType: ?Sized, 
    R: Rule<'input, SliceType>, O, E: Error + 'static,
    Func: Fn(R::Output) -> Result<O, E>
> Rule<'input, SliceType> for TryMap<'input, SliceType, R, O, E, Func> {
    type Output = O;

    fn parse_at<'cursor, 'this, 'index>(&'this self, input: &'cursor mut &'input SliceType, index: &'index mut usize)
        -> Result<Self::Output, ParseError> where 'input: 'this 
    {
        let start_index = *index;
        let start_input = *input;
        self.inner.parse_at(input, index)
            .and_then(|res| (self.func)(res)
                .map_err(|err| {
                    *index = start_index;
                    *input = start_input;
                    ParseError::new(Some(Box::new(err)), self.inner.name(), start_index)
                })
            )
    }
}


/// Errors if a rule matches.  See [`Rule::prevent`].
#[derive(Debug, Clone, PartialEq, NamedRule)]
pub struct Not<R>(pub(crate) R);

impl<'input, T: ?Sized + 'input, R: Rule<'input, T>> Rule<'input, T> for Not<R> {
    type Output = ();

    fn parse_at<'cursor, 'this, 'index>(&'this self, input: &'cursor mut &'input T, index: &'index mut usize) -> Result<Self::Output, ParseError> where 'input: 'this {
        let start = *index;
        let res = self.0.parse_at(input, index);
        *index = start;
        let Err(_) = res else {
            return Err(ParseError::new(
                Some(Box::new(UnexpectedMatch)),
                self.name(), start
            ));
        };
        Ok(())
    }
}

/// Attempts to parse a rule, returning its result. See [`Rule::attempt`].
#[derive(NamedRule)]
pub struct Attempt<'input, T: 'input + ?Sized, R: Rule<'input, T>>(pub R, pub(crate) PhantomData<&'input T>);

impl<'input, T: 'input + ?Sized, R: Rule<'input, T>> Rule<'input, T> for Attempt<'input, T, R> {
    type Output = Result<R::Output, ParseError>;
    
    fn parse_at<'cursor, 'this, 'index>(&'this self, input: &'cursor mut &'input T, index: &'index mut usize) -> Result<Self::Output, ParseError> where 'input: 'this {
        // core::array::try_from_fn(|_| self.0.parse_at(input, index))
        let before = (*input, *index);
        let res = self.0.parse_at(input, index);
        if res.is_err() { (*input, *index) = before; }
        Ok(res)
    }
}

/// Matches a rule forever, failing if it does. See [`Rule::consume_all`].
#[derive(NamedRule)]
pub struct Consume<'input, T: 'input + ?Sized, R: Rule<'input, T>>(pub R, pub(crate) PhantomData<&'input T>);

impl<'input, R: Rule<'input, str>> Rule<'input, str> for Consume<'input, str, R> {
    type Output = Vec<R::Output>;
    
    fn parse_at<'cursor, 'this, 'index>(&'this self, input: &'cursor mut &'input str, index: &'index mut usize) -> Result<Self::Output, ParseError> where 'input: 'this {
        // core::array::try_from_fn(|_| self.0.parse_at(input, index))
        let before = (*input, *index);
        let mut els = Vec::new();
        while !input.is_empty() {
            let el = match self.0.parse_at(input, index) {
                Ok(v) => v,
                Err(err) => { (*input, *index) = before; return Err(err); }
            };
            els.push(el);
        }
        Ok(els)
    }
}
impl<'input, T: 'input, R: Rule<'input, [T]>> Rule<'input, [T]> for Consume<'input, [T], R> {
    type Output = Vec<R::Output>;
    
    fn parse_at<'cursor, 'this, 'index>(&'this self, input: &'cursor mut &'input [T], index: &'index mut usize) -> Result<Self::Output, ParseError> where 'input: 'this {
        // core::array::try_from_fn(|_| self.0.parse_at(input, index))
        let before = (*input, *index);
        let mut els = Vec::new();
        while !input.is_empty() {
            let el = match self.0.parse_at(input, index) {
                Ok(v) => v,
                Err(err) => { (*input, *index) = before; return Err(err); }
            };
            els.push(el);
        }
        Ok(els)
    }
}

/// Repeatedly matches a rule a known amount of times. See [`Rule::repeat_for`].
#[derive(NamedRule)]
pub struct RepeatFor<'input, T: 'input + ?Sized, R: Rule<'input, T>, const REPETITIONS: usize>(pub R, pub(crate) PhantomData<&'input T>);
impl<'input, T: 'input + ?Sized, R: Rule<'input, T>, const REPETITIONS: usize> Rule<'input, T> for RepeatFor<'input, T, R, REPETITIONS> {
    type Output = [R::Output; REPETITIONS];
    
    fn parse_at<'cursor, 'this, 'index>(&'this self, input: &'cursor mut &'input T, index: &'index mut usize) -> Result<Self::Output, ParseError> where 'input: 'this {
        // core::array::try_from_fn(|_| self.0.parse_at(input, index))
        let before = (*input, *index);
        let mut arr: [Option<R::Output>; REPETITIONS] = [const { None }; REPETITIONS];
        for el in &mut arr {
            el.replace(match self.0.parse_at(input, index) {
                Ok(v) => v,
                Err(err) => {
                    (*input, *index) = before;
                    return Err(err);
                }
            });
        }
        Ok(arr.map(|v| v.unwrap()))
    }
}

/// Matches a rule a set amount of times. See [`Rule::repeat`]
#[derive(NamedRule)]
pub struct Repeat<'input, T: 'input + ?Sized, R: Rule<'input, T>>(pub R, pub usize, pub(crate) PhantomData<&'input T>);
impl<'input, T: 'input + ?Sized, R: Rule<'input, T>> Rule<'input, T> for Repeat<'input, T, R> {
    type Output = Vec<R::Output>;
    
    fn parse_at<'cursor, 'this, 'index>(&'this self, input: &'cursor mut &'input T, index: &'index mut usize) -> Result<Self::Output, ParseError> where 'input: 'this {
        // core::array::try_from_fn(|_| self.0.parse_at(input, index))
        let before = (*input, *index);
        let mut arr = Vec::with_capacity(self.1);
        for _ in 0..self.1 {
            arr.push(match self.0.parse_at(input, index) {
                Ok(v) => v,
                Err(err) => {
                    (*input, *index) = before;
                    return Err(err);
                }
            });
        }
        Ok(arr)
    }
}

/// Matches a rule an arbitrary amount of times. See [`Rule::take`].
#[derive(NamedRule)]
pub struct Many<'input, T: 'input + ?Sized, R: Rule<'input, T>> {
    rule: R,
    limit: Option<usize>,
    _p: PhantomData<&'input T>
}

impl<'input, T: 'input + ?Sized, R: Rule<'input, T>> Many<'input, T, R> {
    /// Matches a potentially infinite amount of times
    pub fn unlimited(rule: R) -> Self {
        Self { rule, limit: None, _p: PhantomData }
    }

    /// Matches at most a set amount of times.
    pub fn limited(rule: R, limit: usize) -> Self {
        Self { rule, limit: Some(limit), _p: PhantomData }
    }
}

impl<'input, T: 'input + ?Sized, R: Rule<'input, T>> Rule<'input, T> for Many<'input, T, R> {
    type Output = Vec<R::Output>;
    
    fn parse_at<'cursor, 'this, 'index>(&'this self, input: &'cursor mut &'input T, index: &'index mut usize) -> Result<Self::Output, ParseError> where 'input: 'this {
        // core::array::try_from_fn(|_| self.0.parse_at(input, index))
        let mut arr = Vec::new();
        let mut i = 0;
        while let Ok(res) = self.rule.parse_at(input, index) {
            arr.push(res);
            i += 1;
            if self.limit.is_some_and(|limit| limit >= i) {
                break;
            }
        }
        Ok(arr)
    }
}

/// Matches one of any character or slice member. Fails on empty input.
/// 
/// # Example
/// ```ignore
/// Double: (char, char) = Any, arg_0;
/// ```
#[derive(Debug, Copy, Clone, NamedRule)]
pub struct Any;
impl<'input, T: 'input> Rule<'input, [T]> for Any {
    type Output = &'input T;

    fn parse_at<'cursor, 'this, 'index>(&'this self, input: &'cursor mut &'input [T], index: &'index mut usize) -> Result<Self::Output, ParseError> where 'input: 'this {
        (!input.is_empty())
            .then(|| {
                let source = &input[0];
                *input = &input[1..];
                *index += 1;
                source
            })
            .ok_or(ParseError::new(Some(Box::new(UnexpectedEOF)), self.name(), *index))
    }
}

impl<'input> Rule<'input, str> for Any {
    type Output = char;

    fn parse_at<'cursor, 'this, 'index>(&'this self, input: &'cursor mut &'input str, index: &'index mut usize) -> Result<Self::Output, ParseError> where 'input: 'this {
        input.chars().next()
            .inspect(|chr| {
                let len = chr.len_utf8();
                *input = &input[len..];
                *index += len;
            })
            .ok_or(ParseError::new(Some(Box::new(UnexpectedEOF)), self.name(), *index))
    }
}

/// Takes input until a given function fails.
/// 
/// # Example
/// ```ignore
/// number: &'input str = While::from(char::is_ascii_digit)
/// ```
#[derive(Debug, Clone, PartialEq, NamedRule)]
pub struct While<F, T> { func: F, _p: PhantomData<T> }

impl<T, F: Fn(&T) -> bool> While<F, T> {
    /// Creates a [`While`] rule from a function. 
    pub fn from(func: F) -> Self {
        Self { func, _p: PhantomData }
    }
}

impl<'input, F: Fn(&char) -> bool> Rule<'input, str> for While<F, char> {
    type Output = &'input str;

    fn parse_at<'cursor, 'this, 'index>(&'this self, input: &'cursor mut &'input str, index: &'index mut usize)
        -> Result<Self::Output, ParseError> where 'input: 'this
    {
        let offset = input.find(|c: char| !(self.func)(&c))
            .unwrap_or(input.len());

        let res = &input[..offset];
        *input = &input[offset..];
        *index += offset;
        Ok(res)
    }
}

impl<'input, T: 'input, F: Fn(&T) -> bool> Rule<'input, [T]> for While<F, T> {
    type Output = &'input [T];

    fn parse_at<'cursor, 'this, 'index>(&'this self, input: &'cursor mut &'input [T], index: &'index mut usize)
        -> Result<Self::Output, ParseError> where 'input: 'this
    {
        let offset = (*input).iter().position(|c: &T| !(self.func)(c))
            .unwrap_or(input.len());

        let res = &input[..offset];
        *input = &input[offset..];
        *index += offset;
        Ok(res)
    }
}

/// Struct returned by [`Rule::spanned`] to store the span and source of a given parsed rule.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Span<'input, T: 'input + ?Sized, O> {
    /// The range of the input that the rule parsed over.
    pub span: Range<usize>,
    /// The original input that the rule parsed.
    pub source: &'input T,
    /// The output of the rule's parsing.
    pub output: O
}

/// Records the span of a given rule. See [`Rule::spanned`].
#[derive(NamedRule)]
pub struct Spanned<'input, T: 'input + ?Sized, R: Rule<'input, T>> { pub(crate) rule: R, pub(crate) _p: PhantomData<&'input T> }

impl<'input, T: 'input + Index<RangeTo<usize>, Output = T> + ?Sized, R: Rule<'input, T>> Rule<'input, T> for Spanned<'input, T, R> {
    type Output = Span<'input, T, R::Output>;
    
    fn parse_at<'cursor, 'this, 'index>(&'this self, input: &'cursor mut &'input T, index: &'index mut usize) -> Result<Self::Output, ParseError> where 'input: 'this {
        let before = (*input, *index);
        let res = self.rule.parse_at(input, index)?;
        Ok(Span {
            span: before.1 .. *index,
            source: &before.0[..*index - before.1],
            output: res
        })
    }
}


/// Always fails with a given error.
/// 
/// # Example
/// ```ignore
/// uh_oh: u32 = Fail::new(Error::new("oh no!"))
/// ```
#[derive(Debug, PartialEq, NamedRule)]
pub struct Fail<E: core::error::Error + Clone + 'static>(pub E);

impl<E: core::error::Error + Clone + 'static> Fail<E> {
    /// Creates a new instance of this type.
    #[inline]
    pub fn new(err: E) -> Self {
        Self(err)
    }
}

impl<'input, T: ?Sized + 'input, E: core::error::Error + Clone + 'static> Rule<'input, T> for Fail<E> {
    type Output = crate::Never;

    fn parse_at<'cursor, 'this, 'index>(&'this self, _input: &'cursor mut &'input T, index: &'index mut usize)
        -> Result<Self::Output, ParseError> where 'input: 'this
    {
        Err(ParseError::new(Some(Box::new(self.0.clone())), self.name(), *index))
    }
}

/// Alias for a refernce to a `dyn` Rule object of a given type and output.
/// 
/// You can use this with an `as` cast in a `match` statement to allow each statement to be a separate rule:
/// ```ignore
/// t: (char, char) = Any, match arg_0 {
///     'a' => &'b' as AnyRule<str, char>,
///     'b' => &Any as AnyRule<str, char>,
///     other => &Fail(Unexpected::new(other)) as AnyRule<str, char>
/// };
/// ```
pub type AnyRule<'rule, 'input, In, Out> = &'rule dyn Rule<'input, In, Output = Out>;
