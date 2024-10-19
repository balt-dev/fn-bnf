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
that uses a BNF-like syntax with the `define!` macro to allow for
using arbitrary Rust items as grammar rules, 
and for parsing both `str`s and any `[T]` (for example, `[u8]` or `[Token]`).

# Feature flags

This crate has two feature flags:
- `more_tuple_impls`, raising the amount of elements `Rule` is implemented for
on tuples of `Rule`s from 16 to 256 - however, enabling this will raise compilation times dramatically
- `error_in_core`, enabling use of this library before Rust 1.81.0 on `nightly` compilers - 
  however, continued support for versions below 1.81.0 is not guaranteed

# A note about the stack

This library's very lifeblood is deep - and likely recursive - function calls.
You may run into stack overflow issues if you have an overly complex grammar, or are blindly parsing malicious input.

# Example

```rust
use fn_bnf::{define, Any, Rule, While, Fail, errors::Unexpected};

#[derive(Debug, PartialEq, Copy, Clone)]
pub enum Token {
    Number(f64),
    Plus, Minus, Asterisk, Slash, Carat, Percent, Ans,
    LeftParen, RightParen
}

define! {
    grammar MathTokens<str> {
        // Mapping the individual parses to () makes .hoard() create a Vec<()>, which doesn't allocate
        WhitespaceToken -> () = _ (' ', '\n', '\t');
        Whitespace -> () = _ WhitespaceToken, _ WhitespaceToken.hoard();

        pub LangTokens -> Vec<Token> = LangToken.consume_all()
            .map_parsed(|v| v.into_iter().filter_map(|v| v).collect() );
        LangToken -> Option<Token> = 
            Num : Plus : Minus : Asterisk : Slash : Percent : Carat
            : LParen : RParen : Ans : _ Whitespace 
            : InvalidChar;
        // Since Fail returns !, we can coerce from that to a token
        InvalidChar -> Token from(|_, n| n) = Any, Fail::new(Unexpected::new(arg_0));

        Plus -> Token = '+'.map_parsed(|_| Token::Plus);
        Minus -> Token = '-'.map_parsed(|_| Token::Minus);
        Asterisk -> Token = '*'.map_parsed(|_| Token::Asterisk);
        Slash -> Token = '/'.map_parsed(|_| Token::Slash);
        Percent -> Token = '%'.map_parsed(|_| Token::Percent);
        Carat -> Token = '^'.map_parsed(|_| Token::Carat);
        LParen -> Token = '('.map_parsed(|_| Token::LeftParen);
        RParen -> Token = ')'.map_parsed(|_| Token::RightParen);

        Ans -> Token = "ans".map_parsed(|_| Token::Ans);

        Num -> Token from(|n| Token::Number(n)) = 
            ("nan", "NaN").map_parsed(|_| f64::NAN) : 
            ("inf", "Infinity").map_parsed(|_| f64::INFINITY) : 
            Float;
        Float -> f64 try_from(f64::from_str) = FloatTokens.spanned().map_parsed(|span| span.source);
        
        FloatTokens -> () = _ UInt, _ FloatFract.attempt(), _ FloatExp.attempt();
        FloatFract -> () = _ '.', _ UInt;
        FloatExp -> () = _ ('e', 'E'), _ ('-', '+').attempt(), _ UInt;

        UInt -> &'input str = While::from(char::is_ascii_digit);
    }
}

define! {
    grammar TokenMath<[Token]> {
        pub Expr -> f64 from(parse_expr) = Prod, SumSuf.consume_all();

        EOF -> () = Rule::<'input, [Token]>::prevent(Any);
        Sum -> f64 from(parse_expr) = Prod, SumSuf.hoard();
        SumSuf -> (&'input [Token], f64) = ([Token::Plus], [Token::Minus]), Prod;
        Prod -> f64 from(parse_expr) = Exp, ProdSuf.hoard();
        ProdSuf -> (&'input [Token], f64) = ([Token::Asterisk], [Token::Slash], [Token::Percent]), Exp;
        Exp -> f64 from(parse_expr) = Neg, ExpSuf.hoard();
        ExpSuf -> (&'input [Token], f64) = [Token::Carat], Neg;
        Neg -> f64 from(|negative, num: f64| if negative {-num} else {num}) 
            = [Token::Minus].attempt().map_parsed(|opt| opt.is_ok()), Atom;
        Atom -> f64 = _ [Token::LeftParen], Sum, _ [Token::RightParen] : Number;
        Number -> f64 try_from(|token: &Token| {
            let Token::Number(n) = token else { return Err(Unexpected::<Token>::new(*token)); };
            Ok(*n)
        }) = Any;
    }
}

fn parse_expr(mut lhs: f64, suffixes: Vec<(&[Token], f64)>) -> f64 {
    for (op, rhs) in suffixes {
        match op[0] {
            Token::Plus => lhs += rhs,
            Token::Minus => lhs -= rhs,
            Token::Asterisk => lhs *= rhs,
            Token::Slash => lhs /= rhs,
            Token::Percent => lhs %= rhs,
            Token::Carat => lhs = lhs.powf(rhs),
            _ => unreachable!()
        }
    }
    lhs
}
```

# Licensing

This crate is dual-licensed under the Apache 2.0 or MIT licenses.