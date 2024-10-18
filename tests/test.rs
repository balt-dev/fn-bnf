use fn_bnf::*;

#[derive(Copy, Clone, PartialEq, Eq, Debug)]
enum Delimiter {
    Parentheses,
    Brackets,
    Braces,
    Angle
}
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
impl NamedRule for Delimiter {
    fn name(&self) -> Option<&'static str> { Some(match self {
        Delimiter::Parentheses => "Delimiter::Parentheses",
        Delimiter::Brackets => "Delimiter::Brackets",
        Delimiter::Braces => "Delimiter::Braces",
        Delimiter::Angle => "Delimiter::Angle",
    }) }
}
/// SAFETY: We're just passing along the parsing to a char, this is fine
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
            delimited: (Delimiter, char) =
                Any.try_map_parsed(Delimiter::try_from),
                Any,
                _ arg_0;
        }
    }

    assert_eq!(Test::delimited.parse("(A)").unwrap().1, (Delimiter::Parentheses, 'A'));
    assert_eq!(Test::delimited.parse("[A]").unwrap().1, (Delimiter::Brackets, 'A'));
    assert_eq!(Test::delimited.parse("{A}").unwrap().1, (Delimiter::Braces, 'A'));
    assert_eq!(Test::delimited.parse("<A>").unwrap().1, (Delimiter::Angle, 'A'));
    assert!(Test::delimited.parse("(A]").is_err());
    assert!(Test::delimited.parse("()").is_err());
}