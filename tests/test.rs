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

#[test]
fn sep_test() {

    define! {
        grammar Test<str> {
            Value -> char = _ '!'.prevent(), Any;
            pub CSVMax<const LIM: usize> -> Vec<(char, Option<char>)> = Value.take_sep(',', LIM);
            pub CSV -> Vec<(char, Option<char>)> = _ '!'.prevent(), Value.hoard_sep(',');
        }
    }
    assert_eq!(Test::CSVMax::<2>.parse("a,b,c,d,e").unwrap().1, vec![('a', Some(',')), ('b', Some(','))]);
    assert_eq!(Test::CSVMax::<2>.parse("a,bc,d,e").unwrap().1, vec![('a', Some(',')), ('b', None)]);
    assert_eq!(Test::CSVMax::<2>.parse("ab,c,d,e").unwrap().1, vec![('a', None)]);
    assert_eq!(Test::CSVMax::<2>.parse("a,!,c,d,e").unwrap().1, vec![('a', Some(','))]);
    assert_eq!(Test::CSV.parse("a,b,c,d,e").unwrap().1, vec![('a', Some(',')), ('b', Some(',')), ('c', Some(',')), ('d', Some(',')), ('e', None)]);
}

use std::{cell::OnceCell, marker::PhantomData, str::FromStr};

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


#[test]
fn action_test() {
    let mut i = 0;
    let action = Action::new(move || { let t = i; i += 1; t });
    let mut idx = 0;
    assert_eq!(action.parse_at(&mut "", &mut idx).unwrap(), 0);
    assert_eq!(action.parse_at(&mut "", &mut idx).unwrap(), 1);
    assert_eq!(action.parse_at(&mut "", &mut idx).unwrap(), 2);
    let other_action = &action;
    assert_eq!(other_action.parse_at(&mut "", &mut idx).unwrap(), 3);
    assert_eq!(action.parse_at(&mut "", &mut idx).unwrap(), 4);
    assert_eq!(idx, 0)
}

thread_local! {
    static ACTION: Action<(), fn()> = Action::new(foo);
}

#[test]
#[should_panic]
fn foo() {
    ACTION.with(|a| { let _res = a.parse(""); });
}
