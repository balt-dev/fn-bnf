use indexmap::{IndexMap, IndexSet};
use proc_macro::TokenStream;
use proc_macro_error::{Diagnostic, Level};
use std::default::Default;
use proc_macro2::Span;
use quote::quote;
use syn::{
    ext::IdentExt, parse::{Parse, ParseStream}, parse_macro_input, punctuated::Punctuated, spanned::Spanned, token, AngleBracketedGenericArguments as GenericArgs, Attribute, Expr, ExprLit, Generics, Ident, Lit, LitInt, RangeLimits, Stmt, Token, Type, Visibility
};
use itertools::Itertools;

mod kw {
    syn::custom_keyword!(grammar);
}

/*
Rough API:

fn parse_int(&mut self, input: &mut &str, start: usize)
    -> Result<TokenTree, ParseError>
{
    // uhh parse an integer here idk
}

define! {
    pub grammar(str) Grammar {
        <hello> = [3..5] <world> parse_int;
        <world> = * "hello";
    }
}

mod __#ident {
    impl crate::Rule<Rule, str> for Rule {
        fn parse(&mut self, input: &mut &str, start: usize)
            -> Result<TokenTree, ParseError>
        {
            let original = *input;
            let mut span = (start) .. (start);
            let mut children = vec![];

            match *self {
                Rule::hello => 'b: {
                    {
                        if let Ok(res) = || {
                            {
                                // if repetitions is none, don't emit loop
                                // if repetitions is unbounded on left, treat as 0..
                                // if repetitions is bounded on start: (3..)
                                for _ in 0 .. 3 {
                                    let token = Rule::world.parse(input, span.end)?;
                                    span.end = token.span.end;
                                // if silent, don't emit
                                    children.push(token);
                                }
                                for _ in 3 .. { // if bounded on both (3..5), do that here
                                    let Ok(token) =
                                        Rule::world.parse(input, span.end)?
                                        else { break; }
                                    span.end = token.span.end;
                                // if silent, don't emit
                                    children.push(token);
                                }
                            }
                        }() { break 'b; }
                    }

                }
            }

            Ok(TokenTree { rule: *self, span, children, source: &original[..(span.end - span.start)] })
        }
    }

    pub enum Rule {
        hello, world
    }
}

pub use __#ident::Rule as #ident;

NOTE: A left-recursive grammar should be a _compilation error!_
They're not super hard to detect, so it'd be better if they were.
 */

#[derive(Debug)]
struct Grammar {
    attrs: Vec<Attribute>,
    vis: Visibility,
    grammar_token: kw::grammar,
    ident: Ident,
    ty: Type,
    brace_token: token::Brace,
    rules: IndexMap<Ident, RuleBody>,
}

impl Parse for Grammar {
    fn parse(input: ParseStream) -> syn::Result<Self> {
        let attrs = input.call(Attribute::parse_outer)?;
        let vis: Visibility = input.parse()?;
        let grammar_token = input.parse::<kw::grammar>()?;
        let ident: Ident = input.parse()?;
        input.parse::<Token![<]>()?;
        let ty: Type = input.parse()?;
        input.parse::<Token![>]>()?;
        let body;
        let brace_token = syn::braced!(body in input);
        let mut rules = IndexMap::new();

        while !body.is_empty() {
            body.parse::<Token![<]>()?;
            let name = body.call(Ident::parse_any)?;
            let generics = Generics::parse(&body)?;
            body.parse::<Token![>]>()?;
            body.parse::<Token![=]>()?;
            let definition = body.parse::<RuleGroup>()?;
            body.parse::<Token![;]>()?;
            let span = name.span();

            if let Some(
                RuleBody { generics: dupe_generics, span: dupe_span, .. }
            ) = rules.insert(name,
                RuleBody { generics: generics.clone(), span, group: definition }
            ) {
                let mut def = Diagnostic::spanned(span, Level::Error, "cannot have duplicate rules".into())
                    .span_note(dupe_span, "first definition of rule here".into());
                if generics != dupe_generics {
                    def = def.note("no two rules, even with differing generic arguments, may have the same name".into())
                             .note("this restriction may be lifted in the future".into());
                }
                def.abort();
            }
        }

        Ok(Grammar {
            attrs,
            vis, grammar_token,
            ident,
            ty, brace_token,
            rules,
        })
    }
}

#[derive(Debug)]
struct RuleGroup {
    options: Punctuated<RulePath, Token![:]>,
}

impl Parse for RuleGroup {
    fn parse(input: ParseStream) -> syn::Result<Self> {
        Punctuated::<RulePath, Token![:]>::parse_separated_nonempty(input).map(|options| Self { options })
    }
}

#[derive(Debug)]
struct RulePath {
    elements: Punctuated<RuleElement, Token![,]>,
}

impl Parse for RulePath {
    fn parse(input: ParseStream) -> syn::Result<Self> {
        Ok(Self {
            elements: Punctuated::<RuleElement, Token![,]>::parse_separated_nonempty(input)?
        })
    }
}

#[derive(Debug)]
struct RuleElement {
    ty: RuleElementTy,
    silent: bool,
    repetitions: (usize, RangeLimits, Option<usize>),
}

impl RuleElement {
    fn tokenize(&self) -> Vec<Stmt> {
        vec![] // TODO
    }
}

#[derive(Debug)]
enum RuleElementTy {
    Rule(Ident, Option<GenericArgs>),
    Callable(Expr),
    Group(Box<RuleGroup>),
}

// *[..5] "hello"
impl Parse for RuleElement {
    fn parse(input: ParseStream) -> syn::Result<Self> {
        let mut silent = false;
        let mut repetitions = (1, RangeLimits::Closed(Default::default()), Some(1));
        if input.peek(Token![*]) {
            input.parse::<Token![*]>()?;
            silent = true;
        }
        if input.peek(syn::token::Bracket) {
            let expr = input.parse::<syn::ExprArray>()?;
            if expr.elems.len() != 1 {
                return Err(syn::Error::new(expr.span(), "malformed repetition count"));
            }
            let Some(Expr::Range(range)) = expr.elems.first() else {
                return Err(syn::Error::new(expr.span(), "repetition count must be a range"));
            };
            let mut range = range.clone();
            let start = range.start.get_or_insert_with(||
                Box::new(Expr::Lit(ExprLit {
                    attrs: vec![],
                    lit: Lit::Int(LitInt::new("0", range.limits.span()))
                })
            ));
            let Expr::Lit(ExprLit { lit: Lit::Int(ref int), .. }) = &**start else {
                return Err(syn::Error::new(start.span(), "repetition bounds must be integer literals"));
            };
            let start: usize = int.base10_parse()?;
            let mut end: Option<usize> = None;
            if let Some(ref e) = range.end {
                let Expr::Lit(ExprLit { lit: Lit::Int(ref int), .. }) = &**e else {
                    return Err(syn::Error::new(start.span(), "repetition bounds must be integer literals"));
                };
                let e = int.base10_parse()?;
                if e < start {
                    Diagnostic::spanned(range.span(), Level::Error, "repetition count end cannot be greater than start".into())
                        .abort();
                }
                if matches!(range.limits, RangeLimits::HalfOpen(..)) && start == e {
                    Diagnostic::spanned(range.span(), Level::Warning, "will match 0 times".into())
                        .emit();
                }
                end = Some(e);
                
            }
            repetitions = (start, range.limits, end);
        }
        let ty = if input.peek(syn::token::Paren) {
            let inner;
            syn::parenthesized!(inner in input);
            let group = inner.parse()?;
            RuleElementTy::Group(Box::new(group))
        } else if input.peek(Token![<]) {
            input.parse::<Token![<]>()?;
            let name = input.call(Ident::parse_any)?;
            let mut args = None;
            if input.peek(Token![::]) {
                args = Some(input.call(GenericArgs::parse_turbofish)?);
            }
            input.parse::<Token![>]>()?;
            RuleElementTy::Rule(name, args)
        } else {
            let expr: Expr = match input.parse() {
                Ok(v) => v,
                Err(err) => Diagnostic::spanned(err.span(), Level::Error, "invalid rule component".into()).note("expected an expression or rule name".into()).abort()
            };
            RuleElementTy::Callable(expr)
        };

        Ok(RuleElement { ty, silent, repetitions })
    }
}

#[derive(Debug)]
struct RuleBody {
    generics: Generics,
    span: Span,
    group: RuleGroup
}

fn check_left_recursion(rules: &IndexMap<Ident, RuleBody>, group: &RuleGroup, seen: &IndexSet<Ident>) {
    for option in group.options.iter() {
        let Some(rule) = option.elements.first() else { continue; };
        match &rule.ty {
            RuleElementTy::Callable(_) => (),
            RuleElementTy::Group(group) => {
                check_left_recursion(rules, group, seen);
            }
            RuleElementTy::Rule(ident, _) => {
                let Some(RuleBody { group: def, .. }) = rules.get(ident) else {
                    Diagnostic::spanned(ident.span(), Level::Error, "rule does not exist".into()).abort()
                };
                let mut seen = seen.clone();
                let (index, exists) = seen.replace_full(ident.clone());
                if let Some(dupe) = exists {
                    Diagnostic::spanned(dupe.span(), Level::Error, "left recursion detected".into()).note(format!(
                        "call chain: {}, <{dupe}>",
                        seen.iter().skip(index).map(|id| format!("<{id}>")).collect::<Vec<_>>().join(", ")
                    )).abort();
                }
                check_left_recursion(rules, def, &seen);
            }
        }
    }
}

#[proc_macro_error::proc_macro_error]
#[proc_macro]
pub fn define(input: TokenStream) -> TokenStream {
    let Grammar {
        attrs, vis, grammar_token, ident, ty, brace_token, rules
    } = parse_macro_input!(input as Grammar);

    // Detect left recursion
    for (_, RuleBody {group, .. }) in rules.iter() {
        let seen = IndexSet::new();
        check_left_recursion(&rules, group, &seen);
    }

    let mod_name = Ident::new(&format!("__{ident}"), ident.span());

    let rule_names = rules.keys();
    let (names, genrs) = rules.values().map(
        |b| {
            let (a, b, _) = b.generics.split_for_impl();
            (a, b)
        }
    ).tee();
    let rule_generics = genrs.map(|(_, b)| b);
    let rule_generic_names = names.map(|(a, _)| a);
    let rule_groups = rules.values().map(
        |body| body.group.options.iter().map(
            |opt| opt.elements.iter().map(
                |el| el.tokenize()
            ).collect_vec()
        ).collect_vec()
    );

    quote!(
        mod #mod_name {
            use super::*;
            #(
                #[allow(non_camel_case_types)]
                struct #rule_names #rule_generics;

                impl #rule_generic_names ::fn_ebnf::Rule < #ty > for #rule_names #rule_generics {
                    fn parse<'cursor, 'input, 'this: 'input>(&'this self, input: &'cursor mut &'input #ty, start: usize)
                        -> Result<TokenTree<'input, #ty>, ParseError<#ty>>
                    {
                        let orig_input = *input;
                        let mut active_names = vec![];
                        #(
                            match (|| { #( { #( #rule_groups )* } )* } ()) {
                                Ok(tree) => return Ok(tree),
                                Err(err) => {
                                    active_names.extend(&mut err.rule_name());
                                    *input = orig_input
                                }
                            }
                        )*
                        
                        return Err({
                            let err_string = if active_names.is_empty() {
                                format!("expected {}", self.name())
                            } else {
                                format!("expected {}", active_names.join(","))
                            };
                            ParseError::new(Some(stringify!( #rule_names )), err_string)
                        })
                    }
                } 
            )*
        }

        #vis use #mod_name as #ident;
    ).into()
}