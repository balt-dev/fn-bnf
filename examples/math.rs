
use core::{convert::Infallible, num::ParseFloatError};
use std::io::Write;

use fn_bnf::{define, Any, Rule, While};

#[derive(Debug, PartialEq, Copy, Clone)]
enum Token {
    Number(f64),
    Plus, Minus, Asterisk, Slash, Percent, LeftParen, RightParen
}
impl core::fmt::Display for Token {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{self:?}")
    }
}

#[derive(Debug)]
struct InvalidToken(Token);
impl core::fmt::Display for InvalidToken {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "unexpected token: {}", self.0)
    }
}

impl core::error::Error for InvalidToken {}

#[derive(Debug)]
struct InvalidCharacter(char);
impl core::fmt::Display for InvalidCharacter {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "unexpected character: {}", self.0)
    }
}
impl core::error::Error for InvalidCharacter {}

define! {
    grammar MathTokens<str> {
        // Mapping the individual parses to () makes .hoard() create a Vec<()>, which doesn't allocate
        ws_token: () = _ (' ', '\n', '\t');
        whitespace: () = _ ws_token, _ ws_token.hoard();

        tokens: Vec<Token> = token.consume_all().map_parsed(|v| v.into_iter().filter_map(|v| v).collect());
        token: Option<Token> = 
            num : plus : minus : asterisk : slash : percent : lparen : rparen 
            : _ whitespace;

        plus: Token = '+'.map_parsed(|_| Token::Plus);
        minus: Token = '-'.map_parsed(|_| Token::Minus);
        asterisk: Token = '*'.map_parsed(|_| Token::Asterisk);
        slash: Token = '/'.map_parsed(|_| Token::Slash);
        percent: Token = '%'.map_parsed(|_| Token::Percent);
        lparen: Token = '('.map_parsed(|_| Token::LeftParen);
        rparen: Token = ')'.map_parsed(|_| Token::RightParen);

        num: Token from(|n| Ok::<_, Infallible>(Token::Number(n))) 
            = "nan".map_parsed(|_| f64::NAN) : "inf".map_parsed(|_| f64::INFINITY) : float;
        float: f64 from(construct_float) = float_tokens.spanned().map_parsed(|span| span.source);
        
        float_tokens: () = _ uint, _ float_fract.maybe(), _ float_exp.maybe();
        float_fract: () = _ '.', _ uint;
        float_exp: () = _ ('e', 'E'), _ ('-', '+').maybe(), _ uint;

        uint: &'input str = While::from(char::is_ascii_digit);
    }
}

fn construct_float(num: &str) -> Result<f64, ParseFloatError> {
    num.parse()
}

define! {
    grammar TokenMath<[Token]> {
        EOF: () = Rule::<'input, [Token]>::prevent(Any);
        expr: f64 from(parse_expr) = prod, sum_suf.consume_all();
        sum: f64 from(parse_expr) = prod, sum_suf.hoard();
        sum_suf: (&'input [Token], f64) = ([Token::Plus], [Token::Minus]), prod;
        prod: f64 from(parse_expr) = neg, prod_suf.hoard();
        prod_suf: (&'input [Token], f64) = ([Token::Asterisk], [Token::Slash], [Token::Percent]), neg;
        neg: f64 from(|negative, num: f64| Ok::<_, Infallible>(if negative {-num} else {num})) 
            = [Token::Minus].maybe().map_parsed(|opt| opt.is_some()), atom;
        atom: f64 = _ [Token::LeftParen], sum, _ [Token::RightParen] : number;
        number: f64 = Rule::<'input, [Token]>::try_map_parsed(Any, |token| {
            let Token::Number(n) = token else { return Err(InvalidToken(*token)); };
            Ok(*n)
        });
    }
}

fn parse_expr(mut lhs: f64, suffixes: Vec<(&[Token], f64)>) -> Result<f64, Infallible> {
    for (op, rhs) in suffixes {
        match op[0] {
            Token::Plus => lhs += rhs,
            Token::Minus => lhs -= rhs,
            Token::Asterisk => lhs *= rhs,
            Token::Slash => lhs /= rhs,
            Token::Percent => lhs %= rhs,
            _ => unreachable!()
        }
    }
    Ok(lhs)
}


fn main() -> Result<(), std::io::Error> {
    let mut lines = std::io::stdin().lines();
    println!("Input a math expression below, or nothing to exit:");
    loop {
        print!("> ");
        std::io::stdout().flush()?;
        let Some(input) = lines.next() else { break Ok(()) };
        let input = input?;
        if input.is_empty() { break Ok(()); }
        let (_, tokens) = match MathTokens::tokens.parse(&input) {
            Ok(v) => v,
            Err(err) => {
                println!("! Failed to parse: {err}");
                continue;
            }
        };
        let (_, result) = match TokenMath::expr.parse(tokens.as_ref()) {
            Ok(v) => v,
            Err(err) => {
                println!("! Failed to parse: {err}");
                continue;
            }
        };
        println!("< {result}")
    }
}