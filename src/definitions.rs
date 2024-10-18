#[allow(clippy::wildcard_imports)]
use super::*;

#[allow(clippy::needless_lifetimes)] // used in proc macro
impl<'input, T, S: ?Sized> NamedRule for for<'index, 'cursor> fn(&'cursor mut &'input S, &'index mut usize) -> Result<T, ParseError> {
    fn name(&self) -> Option<&'static str> { Some("<anonymous rule>") }
}
impl<'input, T, S: ?Sized> Rule<'input, S> for for<'index, 'cursor> fn(&'cursor mut &'input S, &'index mut usize) -> Result<T, ParseError> {
    type Output = T;

    fn parse_at<'cursor, 'this, 'index>(&'this self, input: &'cursor mut &'input S, index: &'index mut usize) -> Result<T, ParseError> where 'input: 'this {
        let before = (*input, *index);
        self(input, index).map_err(|err| {
            (*input, *index) = before;
            ParseError::new(Some(Box::new(err)), self.name(), *index)
        })
    }
}
impl<T> NamedRule for for<'a> fn(&'a T) -> bool {
    fn name(&self) -> Option<&'static str> { Some("<anonymous pattern>") }
}

/// SAFETY: We only advance if the pattern matches.
impl<'input, T: 'input> Rule<'input, [T]> for for<'a> fn(&'a T) -> bool {
    type Output = &'input T;

    fn parse_at<'cursor, 'this, 'index>(&'this self, input: &'cursor mut &'input [T], index: &'index mut usize) -> Result<Self::Output, ParseError> where 'input: 'this {
        if let Some(first) = input.first().and_then(|v| self(v).then_some(v)) {
            *input = &input[1..];
            *index += 1;
            return Ok(first);
        }
        Err(ParseError::new(Some(Box::new(UnmatchedInput)), self.name(), *index))
    }
}

impl<'input> Rule<'input, str> for fn(&char) -> bool {
    type Output = char;

    fn parse_at<'cursor, 'this, 'index>(&'this self, input: &'cursor mut &'input str, index: &'index mut usize) -> Result<Self::Output, ParseError> where 'input: 'this {
        if let Some((chr, idx)) = input.chars().next().and_then(|chr| self(&chr).then_some((chr, chr.len_utf8()))) {
            *input = &input[idx..];
            *index += idx;
            return Ok(chr);
        }
        Err(ParseError::new(Some(Box::new(UnmatchedInput)), self.name(), *index))
    }
}

impl NamedRule for char {
    fn name(&self) -> Option<&'static str> { Some("<single character literal>") }
}
impl<'input> Rule<'input, str> for char {
    type Output = char;

    fn parse_at<'cursor, 'this, 'index>(&'this self, input: &'cursor mut &'input str, index: &'index mut usize) -> Result<Self::Output, ParseError> where 'input: 'this {
        if let Some((chr, idx)) = input.chars().next().and_then(|chr| (*self == chr).then_some((chr, chr.len_utf8()))) {
            *input = &input[idx..];
            *index += idx;
            return Ok(chr);
        }
        Err(ParseError::new(Some(Box::new(UnmatchedInput)), self.name(), *index))
    }
}

impl<T> NamedRule for [T] {
    fn name(&self) -> Option<&'static str> { Some("<slice literal>") }
}
impl<'input, T: PartialEq + 'input> Rule<'input, [T]> for [T] {
    type Output = &'input [T];

    fn parse_at<'cursor, 'this, 'index>(&'this self, input: &'cursor mut &'input [T], index: &'index mut usize) -> Result<Self::Output, ParseError> where 'input: 'this {
        if let Some(after) = input.strip_prefix(self) {
            let res = &input[..self.len()];
            *input = after;
            *index += self.len();
            Ok(res)
        } else { Err(ParseError::new(Some(Box::new(NoMatch)), self.name(), *index)) }
    }
}

impl<const N: usize, T> NamedRule for [T; N] {
    fn name(&self) -> Option<&'static str> { Some("<array literal>") }
}
impl<'input, const N: usize, T: PartialEq + 'input> Rule<'input, [T]> for [T; N] {
    type Output = &'input [T];

    #[inline]
    fn parse_at<'cursor, 'this, 'index>(&'this self, input: &'cursor mut &'input [T], index: &'index mut usize) -> Result<Self::Output, ParseError> where 'input: 'this {
        self[..].parse_at(input, index)
    }
}

impl NamedRule for str {
    fn name(&self) -> Option<&'static str> { Some("<string literal>") }
}
impl<'input> Rule<'input, str> for str {
    type Output = &'input str;

    fn parse_at<'cursor, 'this, 'index>(&'this self, input: &'cursor mut &'input str, index: &'index mut usize) -> Result<Self::Output, ParseError> where 'input: 'this {
        if let Some(after) = input.strip_prefix(self) {
            let res = &input[..self.len()];
            *input = after;
            *index += self.len();
            Ok(res)
        } else { Err(ParseError::new(Some(Box::new(NoMatch)), self.name(), *index)) }
    }
}

impl<T: ?Sized + NamedRule> NamedRule for &T {
    fn name(&self) -> Option<&'static str> { (*self).name() }
}

impl<'input, S: ?Sized + 'input, T: ?Sized + Rule<'input,  S>> Rule<'input, S> for &T {
    type Output = <T as Rule<'input, S>>::Output;

    fn parse_at<'cursor, 'this, 'index>(&'this self, input: &'cursor mut &'input S, index: &'index mut usize) -> Result<Self::Output, ParseError> where 'input: 'this {
        (**self).parse_at(input, index)
    }
}
