

// thank you
// i'll say goodbye soon
// though it's the end of the world
// don't blame yourself now
//
// and if it's true
// i will surround you
// and give life to a world
// that's our own
//
// porter robinson - goodbye to a world
// 【=◈︿◈=】

use indexmap::IndexMap;
use proc_macro::TokenStream;
use proc_macro_error::{Diagnostic, Level};
use proc_macro2::Span;
use quote::{quote, TokenStreamExt};
use syn::{
    ext::IdentExt,
    parse::{Parse, ParseStream},
    parse_macro_input,
    punctuated::Punctuated,
    spanned::Spanned, Attribute, Expr,
    GenericParam, Generics, Ident, Lifetime, LifetimeParam,
    Stmt, Token, Type, Visibility
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
                RuleBody { generics, fields, ty, func, span, group: definition }
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
            Fields::Unit => tokens.append_all(quote!(;).into_iter()),
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
        self.inner.to_tokens(tokens)
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
    fn tokenize(self, name: &Ident, rule_ty: &Type) -> Vec<Stmt> {
        let Self { mut generics, fields, ty, func, span, group } = self;
        let mut impl_generics = generics.clone();
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
                        bounds: Default::default(),
                        eq_token: None,
                        default: None
                    });
                }
            }
        }
        let mut min_options = None::<usize>;
        let mut max_options = None::<usize>;
        for option in group.options.iter() {
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
            .map(|n| syn::Ident::new_raw(&format!("arg_{n}"), span.clone()))
            .collect_vec();
        let optional_variable_defs = variable_names.iter()
            .skip(min_options)
            .map(|id| -> Stmt {syn::parse_quote_spanned! {span.clone()=> let #id = None;}})
            .collect_vec();
    
        for (i, option) in group.options.iter().enumerate() {
            let at_end = i + 1 >= group.options.len();
            let mut next_args = Vec::<Stmt>::new();

            let return_expr: Expr = if let Some(func) = &func {
                syn::parse_quote_spanned!(
                    span.clone()=> 
                    (#func)(#(#variable_names),*)
                        .map_err(|err| {
                            *index = before_index;
                            *input = before_input;
                            ::fn_bnf::ParseError::new(
                                Some(::fn_bnf::Box::new(err)),
                                ::fn_bnf::get_name_string::<#rule_ty, _>(&rule),
                                *index
                            )
                        }
                    )
                )
            } else {
                syn::parse_quote_spanned!(span=> Ok((#(#variable_names),*)))
            };

            let mut iter = option.elements.iter();
            let Some(first) = iter.next() else {
                element_defs.extend::<Vec<Stmt>>(syn::parse_quote_spanned!(span.clone()=>
                    return #return_expr;
                ));
                break;
            };

            let mut name_iter = variable_names.iter();
            if !first.silent {
                let _ = name_iter.next();
            }

            let fail_condition: Stmt = if at_end {
                syn::parse_quote_spanned!(span.clone()=> {
                    *input = before_input;
                    *index = before_index;
                    return Err(::fn_bnf::ParseError::new(
                        Some(::fn_bnf::Box::new(err)),
                        ::fn_bnf::get_name_string::<#rule_ty, _>(&rule),
                        *index
                    ))
                })
            } else {
                syn::parse_quote_spanned!(span.clone()=> {
                    *input = before_input;
                    *index = before_index;
                    break 'b;
                })
            };

            let names = &mut name_iter;
            let take_count = min_options.saturating_sub((!first.silent) as usize);
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
                next_args.extend::<Vec<Stmt>>(syn::parse_quote_spanned!(el.span()=>
                    let rule = { #el };
                    let #name = match ::fn_bnf::Rule::<'input, #rule_ty>::parse_at(&rule, input, index) {
                        Ok(val) => val,
                        Err(err) => #fail_condition
                    };
                ))
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
                ))
            }

            let maybe_arg0 = (!first.silent).then(|| -> Stmt {
                if first.silent {
                    syn::parse_quote_spanned!(first.span()=> ;)
                } else if min_options == 0 {
                    syn::parse_quote_spanned!(first.span()=> let arg_0 = Some(first);)
                } else {
                    syn::parse_quote_spanned!(first.span()=> let arg_0 = first;)
                }
            }).into_iter();

            element_defs.extend::<Vec<Stmt>>(syn::parse_quote_spanned!(first.span()=> 'b: {
                let before_index = *index;
                let before_input = *input;
                let rule = { #first };
                match ::fn_bnf::Rule::<'input, #rule_ty>::parse_at(&rule, input, index) {
                    Ok(first) => {
                        #(#maybe_arg0)*
                        #(#next_args)*
                        return #return_expr;
                    }
                    Err(err) => #fail_condition
                }
            }));
        }

        syn::parse_quote_spanned!(self.span.clone()=>
            #[allow(non_camel_case_types)]
            #[doc(hidden)]
            pub(super) struct #name #generics #fields

            impl #impl_generics ::fn_bnf::Rule<'input, #rule_ty> for #name #generics 
                where #rule_ty: 'input
            {
                const NAME: Option<&'static str> = Some(stringify!(#name));

                type Output = #ty;

                #[allow(unused_variables, unreachable_code, unused_labels, unused_parens)]
                fn parse_at<'cursor, 'this, 'index>(&'this self, input: &'cursor mut &'input #rule_ty, index: &'index mut usize)
                    -> Result<Self::Output, ::fn_bnf::ParseError>
                    where 'input : 'this
                {
                    #(#optional_variable_defs)*

                    #(#element_defs)*

                    Err(::fn_bnf::ParseError::new(Some(::fn_bnf::Box::new(::fn_bnf::ExhaustedInput)), Self::NAME, *index))
                }
            }
        )
    }
}

#[proc_macro_error::proc_macro_error]
#[proc_macro]
// WHEN WRITING DOCS
// - mention arg_# and its nuances
//   - you can use arg_# as a rule, however if it's conditional you will have to .unwrap()
// - returned references to input have to use the 'input lifetime
pub fn define(input: TokenStream) -> TokenStream {
    let Grammar {
        attrs, vis, ident, ty, rules, ..
    } = parse_macro_input!(input as Grammar);

    let mod_name = Ident::new(&format!("__{ident}"), ident.span());

    // .collect_vec() because quote dum
    let rules = rules.iter().map(|(name, body)| body.clone().tokenize(name, &ty));

    quote!(
        #( #attrs )*
        #[allow(non_snake_case)]
        mod #mod_name {
            #[allow(unused_imports)]
            use super::*;
            #(#(#rules)*)*
        }

        #vis use #mod_name as #ident;
    ).into()
}