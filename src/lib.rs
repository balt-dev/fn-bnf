#![cfg_attr(feature = "new_range", feature(new_range_api))]

#[cfg(not(feature = "new_range"))]
use core::ops::Range;
#[cfg(feature = "new_range")]
use core::range::Range;

#[derive(Default)]
pub struct ParseError {
    pub rule_name: Option<String>,
    pub message: String,
    pub index: usize,
}

impl ParseError {
    pub const fn new(rule_name: Option<String>, message: String, index: usize) -> Self {
        Self { rule_name, message, index }
    }
}



pub struct TokenTree<'input, T: ?Sized> {
    pub rule: Option<Box<dyn Rule<T>>>,
    pub span: Range<usize>,
    pub source: &'input T,
    // IDEA: Maybe some day this could be an iterator so it'd be done lazily and there wouldn't be an allocation. 
    //       That'd be nice.
    pub children: Vec<TokenTree<'input, T>>
}

pub trait Rule<SliceType: ?Sized> {
    fn parse<'cursor, 'input, 'this: 'input>(&'this self, input: &'cursor mut &'input SliceType, start: usize)
        -> Result<TokenTree<'input, SliceType>, ParseError>;
}

impl<S: ?Sized, F> Rule<S> for F
    where F: for<'cursor, 'input> Fn(&'cursor mut &'input S, usize)
        -> Result<TokenTree<'input, S>, ParseError>
{
    fn parse<'cursor, 'input, 'this: 'input>(&'this self, input: &'cursor mut &'input S, start: usize) -> Result<TokenTree<'input, S>, ParseError> {
        self(input, start)
    }
}


impl<T: PartialEq> Rule<[T]> for [T] {
    fn parse<'cursor, 'input, 'this: 'input>(&'this self, input: &'cursor mut &'input [T], start: usize)
         -> Result<TokenTree<'input, [T]>, ParseError>
    {
        if let Some(after) = input.strip_prefix(self) {
            *input = after;
            Ok(TokenTree {
                rule: None,
                span: (start .. start + self.len()).into(),
                source: self,
                children: vec![]
            })
        } else { Err(ParseError::new(None, "failed to parse slice literal".into(), start)) }
    }
}

impl Rule<str> for str {
    fn parse<'cursor, 'input, 'this: 'input>(&'this self, input: &'cursor mut &'input str, start: usize)
         -> Result<TokenTree<'input, str>, ParseError>
    {
        if let Some(after) = input.strip_prefix(self) {
            *input = after;
            Ok(TokenTree {
                rule: None,
                span: (start .. start + self.len()).into(),
                source: self,
                children: vec![]
            })
        } else { Err(ParseError::new(None, format!("expected {self}"), start)) }
    }
}

// pub use fn_bnf_macro::*; 