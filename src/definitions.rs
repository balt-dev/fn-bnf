use super::*;

impl<'input, T, S: ?Sized> Rule<'input, S> for for<'index, 'cursor> fn(&'cursor mut &'input S, &'index mut usize) -> Result<T, ParseError> {
    type Output = T;

    fn parse_at<'cursor, 'this, 'index>(&'this self, input: &'cursor mut &'input S, index: &'index mut usize) -> Result<T, ParseError> where 'input: 'this {
        self(input, index)
    }
}

impl<'input, T: 'input> Rule<'input, [T]> for fn(&T) -> bool {
    type Output = &'input T;

    fn parse_at<'cursor, 'this, 'index>(&'this self, input: &'cursor mut &'input [T], index: &'index mut usize) -> Result<Self::Output, ParseError> where 'input: 'this {
        if let Some(first) = input.get(0).and_then(|v| self(v).then_some(v)) {
            *input = &input[1..];
            *index += 1;
            return Ok(first);
        }
        Err(ParseError::new(Some(Box::new(UnmatchedInput)), None, *index))
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
        Err(ParseError::new(Some(Box::new(UnmatchedInput)), None, *index))
    }
}

impl<'input> Rule<'input, str> for char {
    const NAME: Option<&'static str> = Some("<single character literal>");

    type Output = char;

    fn parse_at<'cursor, 'this, 'index>(&'this self, input: &'cursor mut &'input str, index: &'index mut usize) -> Result<Self::Output, ParseError> where 'input: 'this {
        if let Some((chr, idx)) = input.chars().next().and_then(|chr| (*self == chr).then_some((chr, chr.len_utf8()))) {
            *input = &input[idx..];
            *index += idx;
            return Ok(chr);
        }
        Err(ParseError::new(Some(Box::new(UnmatchedInput)), None, *index))
    }
}

impl<'input, T: PartialEq + 'input> Rule<'input, [T]> for [T] {
    const NAME: Option<&'static str> = Some("<slice literal>");

    type Output = &'input [T];

    fn parse_at<'cursor, 'this, 'index>(&'this self, input: &'cursor mut &'input [T], index: &'index mut usize) -> Result<Self::Output, ParseError> where 'input: 'this {
        if let Some(after) = input.strip_prefix(self) {
            let res = &input[..self.len()];
            *input = after;
            *index += self.len();
            Ok(res)
        } else { Err(ParseError::new(Some(Box::new(NoMatch)), Self::NAME, *index)) }
    }
}

impl<'input, const N: usize, T: PartialEq + 'input> Rule<'input, [T]> for [T; N] {
    const NAME: Option<&'static str> = Some("<slice literal>");

    type Output = &'input [T];

    #[inline]
    fn parse_at<'cursor, 'this, 'index>(&'this self, input: &'cursor mut &'input [T], index: &'index mut usize) -> Result<Self::Output, ParseError> where 'input: 'this {
        self[..].parse_at(input, index)
    }
}

impl<'input> Rule<'input, str> for str {
    const NAME: Option<&'static str> = Some("<string literal>");

    type Output = &'input str;

    fn parse_at<'cursor, 'this, 'index>(&'this self, input: &'cursor mut &'input str, index: &'index mut usize) -> Result<Self::Output, ParseError> where 'input: 'this {
        if let Some(after) = input.strip_prefix(self) {
            let res = &input[..self.len()];
            *input = after;
            *index += self.len();
            Ok(res)
        } else { Err(ParseError::new(Some(Box::new(NoMatch)), Self::NAME, *index)) }
    }
}

impl<'input, S: ?Sized + 'input, T: ?Sized + Rule<'input,  S>> Rule<'input, S> for &T {
    const NAME: Option<&'static str> = <T as Rule<'input, S>>::NAME;

    type Output = <T as Rule<'input, S>>::Output;

    fn parse_at<'cursor, 'this, 'index>(&'this self, input: &'cursor mut &'input S, index: &'index mut usize) -> Result<Self::Output, ParseError> where 'input: 'this {
        (**self).parse_at(input, index)
    }
}