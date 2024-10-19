use fn_bnf::{*, errors::Unexpected};

#[derive(Copy, Clone, PartialEq, Eq, Debug, NamedRule)]
pub enum Delimiter { Parentheses, Brackets, Braces, Angle }
impl TryFrom<char> for Delimiter {
    type Error = Unexpected<char>;

    fn try_from(value: char) -> Result<Self, Self::Error> {
        Ok(match value {
            '(' => Self::Parentheses,
            '[' => Self::Brackets,
            '{' => Self::Braces,
            '<' => Self::Angle,
            _ => return Err(Unexpected::new(value))
        })
    }
}

impl<'input> Rule<'input, str> for Delimiter {
    type Output = char;

    fn parse_at<'cursor, 'this, 'index>(&'this self, input: &'cursor mut &'input str, index: &'index mut usize)
        -> Result<Self::Output, ParseError> where 'input: 'this
    {
        match self {
            Delimiter::Parentheses => ')',
            Delimiter::Brackets => ']',
            Delimiter::Braces => '}',
            Delimiter::Angle => '>',
        }.parse_at(input, index)
    }
}

#[test]
fn delim_test() {

    define! {
        grammar Test<str> {
            pub Delimited -> (Delimiter, char) =
                Any.try_map_parsed(Delimiter::try_from),
                Any,
                _ arg_0;
            pub Double -> (char, char) = Any, arg_0;

            Empty -> () = _ "";
        }
    }
    assert_eq!(Test::Delimited.parse("(A)").unwrap().1, (Delimiter::Parentheses, 'A'));
    assert_eq!(Test::Delimited.parse("[A]").unwrap().1, (Delimiter::Brackets, 'A'));
    assert_eq!(Test::Delimited.parse("{A}").unwrap().1, (Delimiter::Braces, 'A'));
    assert_eq!(Test::Delimited.parse("<A>").unwrap().1, (Delimiter::Angle, 'A'));
    assert!(Test::Delimited.parse("(A]").is_err());
    assert!(Test::Delimited.parse("()").is_err());
    assert!(Test::Double.parse("()").is_err());
    assert!(Test::Double.parse("((").is_ok());
}

use std::{str::FromStr, marker::PhantomData};

define! {
    grammar test_parsing<str> {
        /// Parses a number, potentially surrounded by parentheses.
        ParenNumber -> u32 = _ '(', ParenNumber, _ ')' : Number;
        /// Parses a number.
        Number -> u32 try_from(u32::from_str) =
            While::from(char::is_ascii_digit);


        pub Doubled<'input, R> {rule: R, _p: PhantomData<&'input str>} -> &'input str
            where R: Rule<'input, str, Output = &'input str>
            = &self.rule, _ arg_0;

        Wawa -> (char, char) = Any, match arg_0 {
            'a' => &'b' as AnyRule<'_, 'input, str, char>,
            'b' => &Any as AnyRule<'_, 'input, str, char>,
            other => &Fail::new(Unexpected::new(other)).map_parsed(|i| i as char) // 
                as AnyRule<'_, 'input, str, char>
        };
    }
}