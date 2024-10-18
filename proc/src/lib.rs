#![allow(missing_docs)] // it's the proc macro who gives a shit

use indexmap::IndexMap;
use proc_macro_error::{Diagnostic, Level};
use proc_macro2::Span;
use proc_macro::TokenStream;
use quote::{quote, TokenStreamExt};
use syn::{
    ext::IdentExt, parse::{Parse, ParseStream}, parse_macro_input, punctuated::Punctuated, spanned::Spanned, Attribute, Expr, GenericParam, Generics, Ident, Lifetime, LifetimeParam, Stmt, Token, Type, TypeInfer, Visibility
};
use itertools::Itertools;

mod kw {
    syn::custom_keyword!(grammar);
    syn::custom_keyword!(from);
}

#[derive(Debug)]
struct Grammar {
    attrs: Vec<Attribute>,
    vis: Visibility,
    ident: Ident,
    ty: Type,
    rules: IndexMap<Ident, RuleBody>,
}

impl Parse for Grammar {
    fn parse(input: ParseStream) -> syn::Result<Self> {
        let attrs = input.call(Attribute::parse_outer)?;
        let vis: Visibility = input.parse()?;
        input.parse::<kw::grammar>()?;
        let ident: Ident = input.parse()?;
        input.parse::<Token![<]>()?;
        let ty: Type = input.parse()?;
        input.parse::<Token![>]>()?;
        let body;
        syn::braced!(body in input);
        let mut rules = IndexMap::new();

        while !body.is_empty() {
            let name = body.call(Ident::parse_any)?;
            let generics = Generics::parse(&body)?;
            let mut fields = Fields::Unit;
            if body.peek(syn::token::Brace) {
                fields = Fields::Structured(body.parse()?);
            }
            body.parse::<Token![:]>()?;
            let ty = body.parse::<Type>()?;
            let mut func = None;
            if body.peek(kw::from) {
                body.parse::<kw::from>()?;
                let parens;
                syn::parenthesized!(parens in body);
                func = Some(parens.parse::<syn::Expr>()?);
            }
            let mut where_clause = None;
            if body.peek(Token![where]) {
                where_clause = Some(body.parse::<syn::WhereClause>()?);
            }
            body.parse::<Token![=]>()?;
            let definition = body.parse::<RuleGroup>()?;
            let end = body.parse::<Token![;]>()?;
            let mut span = name.span();
            if let Some(joined) = span.join(end.span) {
                span = joined;
            }

            if let Some(
                RuleBody { span: dupe_span, .. }
            ) = rules.insert(name,
                RuleBody { generics, fields, ty, func, where_clause, span, group: definition }
            ) {
                Diagnostic::spanned(span, Level::Error, "cannot have duplicate rules".into())
                    .span_note(dupe_span, "first definition of rule here".into())
                    .abort();
            }
        }

        Ok(Grammar {
            attrs,
            vis,
            ident,
            ty,
            rules,
        })
    }
}

#[derive(Debug, Clone)]
struct RuleGroup {
    options: Punctuated<RulePath, Token![:]>,
}

impl Parse for RuleGroup {
    fn parse(input: ParseStream) -> syn::Result<Self> {
        Punctuated::<RulePath, Token![:]>::parse_separated_nonempty(input).map(|options| Self { 
            options 
        })
    }
}

#[derive(Debug, Clone)]
enum Fields {
    Unit,
    Structured(syn::FieldsNamed)
}

impl quote::ToTokens for Fields {
    fn to_tokens(&self, tokens: &mut proc_macro2::TokenStream) {
        match self {
            Fields::Unit => tokens.append_all(quote!(;)),
            Fields::Structured(fields) 
                => fields.to_tokens(tokens),
        }
    }
}

#[derive(Debug, Clone)]
struct RuleBody {
    generics: Generics,
    fields: Fields,
    ty: Type,
    func: Option<Expr>,
    where_clause: Option<syn::WhereClause>,
    span: Span,
    group: RuleGroup,
}

#[derive(Debug, Clone)]
struct ElementTy {
    silent: bool,
    inner: Expr
}

impl Parse for ElementTy {
    fn parse(input: ParseStream) -> syn::Result<Self> {
        let silent = input.peek(Token![_]);
        if silent { input.parse::<Token![_]>()?; }
        input.parse().map(|inner| Self { silent, inner })
    }
}

impl quote::ToTokens for ElementTy {
    fn to_tokens(&self, tokens: &mut proc_macro2::TokenStream) {
        self.inner.to_tokens(tokens);
    }
}

#[derive(Debug, Clone)]
struct RulePath {
    elements: Punctuated<ElementTy, Token![,]>,
}

impl Parse for RulePath {
    fn parse(input: ParseStream) -> syn::Result<Self> {
        Ok(Self {
            elements: Punctuated::<ElementTy, Token![,]>::parse_separated_nonempty(input)?
        })
    }
}

impl RuleBody {
    #[allow(clippy::too_many_lines)]
    fn tokenize(self, name: &Ident, rule_ty: &Type) -> Vec<Stmt> {
        let Self { mut generics, fields, ty, func, where_clause, span, group } = self;
        let infer = Type::Infer(TypeInfer { underscore_token: Default::default() });

        let tys = match &ty {
            t @ Type::Tuple(tup) if tup.elems.is_empty() => vec![t],
            Type::Tuple(tup) => tup.elems.iter().collect(),
            other => vec![other]
        }.into_iter();

        let mut impl_generics = generics.clone();
        let rule_generics = impl_generics.clone();
        impl_generics.params.push(GenericParam::Lifetime(
            LifetimeParam::new(Lifetime::new("'input", name.span()))
        ));
        for param in &mut generics.params {
            match param {
                GenericParam::Lifetime(lt) => {
                    lt.colon_token = None;
                    lt.bounds.clear();
                }
                GenericParam::Type(ty) => {
                    ty.colon_token = None;
                    ty.bounds.clear();
                }
                GenericParam::Const(cst) => {
                    *param = GenericParam::Type(syn::TypeParam {
                        attrs: cst.attrs.clone(), 
                        ident: cst.ident.clone(),
                        colon_token: None,
                        bounds: Punctuated::default(),
                        eq_token: None,
                        default: None
                    });
                }
            }
        }
        let mut min_options = None::<usize>;
        let mut max_options = None::<usize>;
        for option in &group.options {
            let count = option.elements.iter().filter(|el| !el.silent).count();
            min_options = Some(min_options.map_or(count, |m| m.min(count)));
            max_options = Some(max_options.map_or(count, |m| m.max(count)));
        }
        let min_options = min_options.unwrap_or(0);
        let max_options = max_options.unwrap_or(0);
        let mut element_defs = Vec::<Stmt>::new();

        element_defs.push(syn::parse_quote!(
            let _ = ("min_options: ", #min_options, "max_options:", #max_options);
        ));

        let variable_names = (0..max_options)
            .map(|n| syn::Ident::new_raw(&format!("arg_{n}"), span))
            .collect_vec();
        let optional_variable_defs = variable_names.iter()
            .skip(min_options)
            .map(|id| -> Stmt {syn::parse_quote_spanned! {span=> let #id = None;}})
            .collect_vec();
    
        for (i, option) in group.options.iter().enumerate() {
            let at_end = i + 1 >= group.options.len();
            let mut next_args = Vec::<Stmt>::new();

            let return_expr: Expr = if let Some(func) = &func {
                syn::parse_quote_spanned!(
                    span=> 
                    (#func)(#(#variable_names),*)
                        .map_err(|err| {
                            (*input, *index) = __before;
                            ::fn_bnf::ParseError::new(
                                Some(::fn_bnf::Box::new(err)),
                                rule.name(),
                                *index
                            )
                        }
                    )
                )
            } else {
                syn::parse_quote_spanned!(span=> Ok((#(#variable_names),*)))
            };
            let mut tys = tys.clone();
            let mut iter = option.elements.iter();
            let Some(first) = iter.next() else {
                element_defs.extend::<Vec<Stmt>>(syn::parse_quote_spanned!(span=>
                    return #return_expr;
                ));
                break;
            };

            let mut name_iter = variable_names.iter();
            if !first.silent {
                let _ = name_iter.next();
            }

            let fail_condition: Stmt = if at_end {
                syn::parse_quote_spanned!(span=> {
                    (*input, *index) = __before;
                    return Err(::fn_bnf::ParseError::new(
                        Some(::fn_bnf::Box::new(err)),
                        rule.name().or(self.name()),
                        *index
                    ))
                })
            } else {
                syn::parse_quote_spanned!(span=> {
                    (*input, *index) = __before;
                    break 'b;
                })
            };

            let names = &mut name_iter;

            let maybe_arg0 = (!first.silent).then(|| -> Stmt {
                if first.silent {
                    syn::parse_quote_spanned!(first.span()=> ;)
                } else {
                    let Some(first_ty) = func.as_ref().map_or_else(|| tys.next(), |_| Some(&infer)) else {
                        Diagnostic::spanned(ty.span(), Level::Error, "returned type count does not match options".into())
                            .abort()
                    };
                    if min_options == 0 {
                        syn::parse_quote_spanned!(first.span()=> let arg_0: #first_ty = Some(first);)
                    } else {
                        syn::parse_quote_spanned!(first.span()=> let arg_0: #first_ty = first;)
                    }
                }
            }).into_iter();

            let take_count = min_options.saturating_sub(usize::from(!first.silent));
            for el in (&mut iter).take(take_count) {
                if el.silent {
                    next_args.extend::<Vec<Stmt>>(syn::parse_quote_spanned!(el.span()=>
                        let rule = { #el };
                        if let Err(err) = ::fn_bnf::Rule::<'input, #rule_ty>::parse_at(&rule, input, index) {
                            #fail_condition
                        };
                    ));
                    continue;
                }
                let Some(name) = names.next() else { break };
                let Some(opt_ty) = func.as_ref().map_or_else(|| tys.next(), |_| Some(&infer)) else {
                    Diagnostic::spanned(ty.span(), Level::Error, "returned type count does not match options".into())
                        .abort()
                };
                next_args.extend::<Vec<Stmt>>(syn::parse_quote_spanned!(el.span()=>
                    let rule = { #el };
                    let #name: #opt_ty = match ::fn_bnf::Rule::<'input, #rule_ty>::parse_at(&rule, input, index) {
                        Ok(val) => val,
                        Err(err) => #fail_condition
                    };
                ));
            }
            for el in &mut iter {
                if el.silent {
                    next_args.extend::<Vec<Stmt>>(syn::parse_quote_spanned!(el.span()=>
                        let rule = { #el };
                        if let Err(err) = ::fn_bnf::Rule::<'input, #rule_ty>::parse_at(&rule, input, index) {
                            #fail_condition
                        };
                    ));
                    continue;
                }
                let Some(name) = names.next() else { break };
                next_args.extend::<Vec<Stmt>>(syn::parse_quote_spanned!(el.span()=>
                    let rule = { #el };
                    let #name = match ::fn_bnf::Rule::<'input, #rule_ty>::parse_at(&rule, input, index) {
                        Ok(val) => Some(val),
                        Err(err) => #fail_condition
                    };
                ));
            }
            
            element_defs.extend::<Vec<Stmt>>(syn::parse_quote_spanned!(first.span()=> 'b: {
                let rule = { #first };
                match ::fn_bnf::Rule::<'input, #rule_ty>::parse_at(&rule, input, index) {
                    Ok(first) => {
                        #(#maybe_arg0)*
                        #(#next_args)*
                        return #return_expr;
                    }
                    Err(err) => {
                        #fail_condition
                    }
                }
            }));
        }

        let predicates = where_clause.as_ref().map(|v| v.predicates.clone());

        syn::parse_quote_spanned!(self.span=>
            #[allow(non_camel_case_types)]
            #[doc(hidden)]
            pub(super) struct #name #rule_generics #where_clause #fields

            impl #rule_generics ::fn_bnf::NamedRule for #name #generics #where_clause {
                fn name(&self) -> Option<&'static str> { Some(stringify!(#name)) }
            }

            impl #impl_generics ::fn_bnf::Rule<'input, #rule_ty> for #name #generics 
                where #rule_ty: 'input, #predicates
            {
                type Output = #ty;

                #[allow(unused_variables, unreachable_code, unused_labels, unused_parens)]
                fn parse_at<'cursor, 'this, 'index>(&'this self, input: &'cursor mut &'input #rule_ty, index: &'index mut usize)
                    -> Result<Self::Output, ::fn_bnf::ParseError>
                    where 'input : 'this
                {
                    #[allow(unused)]
                    type AnyRule<'input, Out> = &'input dyn ::fn_bnf::Rule<'input, #rule_ty, Output = Out>;
                    let __before = (*input, *index);
                    #(#optional_variable_defs)*

                    #(#element_defs)*

                    Err(::fn_bnf::ParseError::new(Some(::fn_bnf::Box::new(::fn_bnf::ExhaustedInput)), self.name(), *index))
                }
            }
        )
    }
}

#[proc_macro]
#[proc_macro_error::proc_macro_error]
pub fn define(input: TokenStream) -> TokenStream {
    let Grammar {
        attrs, vis, ident, ty, rules, ..
    } = parse_macro_input!(input as Grammar);

    let mod_name = Ident::new(&format!("__{ident}"), ident.span());

    // .collect_vec() because quote dum
    let rules = rules.iter().map(|(name, body)| body.clone().tokenize(name, &ty));

    quote!(
        #( #attrs )*
        #[allow(non_snake_case, unsafe_code)]
        mod #mod_name {
            #[allow(unused_imports)]
            use super::*;
            use ::fn_bnf::NamedRule as _;
            #(#(#rules)*)*
        }

        #vis use #mod_name as #ident;
    ).into()
}