use core::ops::{Index, Range, RangeTo};

use super::*;

macro_rules! err {
    ($($name: ident: $message: literal),*) => {$(
        #[derive(Debug)]
        #[doc = $message]
        pub struct $name;
        impl core::fmt::Display for $name {
            fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
                write!(f, $message)
            }
        }
        impl Error for $name {}
    )*};
}

err! {
    UnmatchedInput: "expected input to match function",
    UnexpectedMatch: "matched input unexpectedly",
    NoMatch: "could not match literal",
    UnexpectedEOF: "unexpected end of input",
    ExhaustedInput: "exhausted all parsing options"
}

pub(crate) struct Map<
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


pub(crate) struct TryMap<
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
                    ParseError::new(Some(Box::new(err)), R::NAME, start_index)
                })
            )
    }
}


pub(crate) struct Not<R>(pub(crate) R);

impl<'input, T: ?Sized + 'input, R: Rule<'input, T>> Rule<'input, T> for Not<R> {
    const NAME: Option<&'static str> = Some("Not");

    type Output = ();

    fn parse_at<'cursor, 'this, 'index>(&'this self, input: &'cursor mut &'input T, index: &'index mut usize) -> Result<Self::Output, ParseError> where 'input: 'this {
        let start = *index;
        let res = self.0.parse_at(input, index);
        *index = start;
        let Err(_) = res else {
            return Err(ParseError::new(
                Some(Box::new(UnexpectedMatch)),
                <Self as Rule<'input, T>>::NAME, start
            ));
        };
        Ok(())
    }
}

pub(crate) struct Maybe<R>(pub R);

impl<'input, T: 'input + ?Sized, R: Rule<'input, T>> Rule<'input, T> for Maybe<R> {
    type Output = Option<R::Output>;
    
    fn parse_at<'cursor, 'this, 'index>(&'this self, input: &'cursor mut &'input T, index: &'index mut usize) -> Result<Self::Output, ParseError> where 'input: 'this {
        // core::array::try_from_fn(|_| self.0.parse_at(input, index))
        let before = (*input, *index);
        let res = self.0.parse_at(input, index).ok();
        if res.is_none() { (*input, *index) = before; }
        Ok(res)
    }
}


pub(crate) struct Consume<R>(pub R);

impl<'input, R: Rule<'input, str>> Rule<'input, str> for Consume<R> {
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
impl<'input, T: 'input, R: Rule<'input, [T]>> Rule<'input, [T]> for Consume<R> {
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

/// Repeatedly matches a rule a known amount of times.
pub(crate) struct Repeat<R, const REPETITIONS: usize>(pub R);

impl<'input, T: 'input + ?Sized, R: Rule<'input, T>, const REPETITIONS: usize> Rule<'input, T> for Repeat<R, REPETITIONS> {
    type Output = [R::Output; REPETITIONS];
    
    fn parse_at<'cursor, 'this, 'index>(&'this self, input: &'cursor mut &'input T, index: &'index mut usize) -> Result<Self::Output, ParseError> where 'input: 'this {
        // core::array::try_from_fn(|_| self.0.parse_at(input, index))
        let before = (*input, *index);
        let mut arr: [Option<R::Output>; REPETITIONS] = [const { None }; REPETITIONS];
        for el in arr.iter_mut() {
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

/// Matches a rule an arbitrary amount of times.
pub(crate) struct Many<R> {
    rule: R,
    limit: Option<usize>
}

impl<R> Many<R> {
    /// Matches a potentially infinite amount of times
    pub fn unlimited(rule: R) -> Self {
        Self { rule, limit: None }
    }

    /// Matches at most a set amount of times.
    pub fn limited(rule: R, limit: usize) -> Self {
        Self { rule, limit: Some(limit) }
    }
}

impl<'input, T: 'input + ?Sized, R: Rule<'input, T>> Rule<'input, T> for Many<R> {
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
pub struct Any;
impl<'input, T: 'input> Rule<'input, [T]> for Any {
    const NAME: Option<&'static str> = Some("Any");

    type Output = &'input T;

    fn parse_at<'cursor, 'this, 'index>(&'this self, input: &'cursor mut &'input [T], index: &'index mut usize) -> Result<Self::Output, ParseError> where 'input: 'this {
        (!input.is_empty())
            .then(|| {
                let source = &input[0];
                *input = &input[1..];
                *index += 1;
                source
            })
            .ok_or(ParseError::new(Some(Box::new(UnexpectedEOF)), <Self as Rule<'input, [T]>>::NAME, *index))
    }
}

impl<'input> Rule<'input, str> for Any {
    const NAME: Option<&'static str> = Some("Any");

    type Output = char;

    fn parse_at<'cursor, 'this, 'index>(&'this self, input: &'cursor mut &'input str, index: &'index mut usize) -> Result<Self::Output, ParseError> where 'input: 'this {
        input.chars().next()
            .map(|chr| {
                let len = chr.len_utf8();
                *input = &input[len..];
                *index += len;
                chr
            })
            .ok_or(ParseError::new(Some(Box::new(UnexpectedEOF)), <Self as Rule<str>>::NAME, *index))
    }
}

pub struct While<F, T> { func: F, _p: PhantomData<T> }

impl<T, F: Fn(&T) -> bool> While<F, T> {
    pub fn from(func: F) -> Self {
        Self { func, _p: PhantomData }
    }
}

impl<'input, F: Fn(&char) -> bool> Rule<'input, str> for While<F, char> {
    const NAME: Option<&'static str> = Some("While");
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
    const NAME: Option<&'static str> = Some("While");
    type Output = &'input [T];

    fn parse_at<'cursor, 'this, 'index>(&'this self, input: &'cursor mut &'input [T], index: &'index mut usize)
        -> Result<Self::Output, ParseError> where 'input: 'this
    {
        let offset = (*input).iter().position(|c: &T| !(self.func)(&c))
            .unwrap_or(input.len());

        let res = &input[..offset];
        *input = &input[offset..];
        *index += offset;
        Ok(res)
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Span<'input, T: 'input + ?Sized, O> {
    pub span: Range<usize>,
    pub source: &'input T,
    pub output: O
}

pub(crate) struct Spanned<R> { pub(crate) rule: R }
impl<'input, T: 'input + Index<RangeTo<usize>, Output = T> + ?Sized, R: Rule<'input, T>> Rule<'input, T> for Spanned<R> {
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