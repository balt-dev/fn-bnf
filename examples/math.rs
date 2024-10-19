use std::{str::FromStr, io::Write};

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


fn main() -> Result<(), std::io::Error> {
    let mut lines = std::io::stdin().lines();
    println!("Input a math expression below, `clear` to clear the console, or `exit` / `quit` to exit.");
    println!("You can access the result of the last expression with `ans`.");
    let mut last_ans = None;
    'outer: loop {
        print!("[?] ");
        std::io::stdout().flush()?;
        let Some(input) = lines.next().transpose()? else { break Ok(()) };
        let input = input.trim_ascii();
        if input.is_empty() { print!("\x1b[1A"); continue; }
        match input {
            "clear" => print!("\x1bc"),
            "exit" | "quit" => break Ok(()),
            _ => {
                let (_, mut tokens) = match MathTokens::LangTokens.parse(&input) {
                    Ok(v) => v,
                    Err(err) => {
                        println!("[!] Failed to parse: {err}");
                        continue;
                    }
                };
                for ans in tokens.iter_mut().filter(|t| matches!(t, Token::Ans)) {
                    let Some(answer) = last_ans else {
                        println!("[!] No previous answer exists");
                        continue 'outer;
                    };
                    *ans = Token::Number(answer);
                }
                let (_, result) = match TokenMath::Expr.parse(tokens.as_ref()) {
                    Ok(v) => v,
                    Err(err) => {
                        println!("[!] Failed to parse: {err}");
                        continue;
                    }
                };
                last_ans = Some(result);
                println!("[=] {result:.}")
            } 
        }
    }
}