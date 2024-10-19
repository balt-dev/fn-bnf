#![allow(missing_docs)] // it's the proc macro who gives a shit

use indexmap::IndexMap;
use proc_macro_error::{Diagnostic, Level};
use proc_macro2::Span;
use proc_macro::TokenStream;
use quote::{quote, TokenStreamExt};
use syn::{
    ext::IdentExt, parse::{Parse, ParseStream}, parse_macro_input, punctuated::Punctuated, spanned::Spanned, Attribute, Expr, GenericParam, Generics, Ident, Lifetime, LifetimeParam, Stmt, Type, TypeInfer, Visibility
};
use itertools::Itertools;

mod kw {
    syn::custom_keyword!(grammar);
    syn::custom_keyword!(from);
    syn::custom_keyword!(try_from);
}

fn cr8_name() -> syn::Path {
    use proc_macro_crate::{crate_name, FoundCrate};
    let found_crate = crate_name("fn-bnf").expect("fn-bnf should be present in `Cargo.toml`");

    match found_crate {
        FoundCrate::Itself => syn::parse_quote!( ::fn_bnf ),
        FoundCrate::Name(name) => syn::Path {
            leading_colon: Some(syn::token::PathSep::default()),
            segments: [syn::PathSegment { ident: Ident::new(&name, Span::call_site()), arguments: syn::PathArguments::None }]
                .into_iter().collect()
        }
    }
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
        input.parse::<syn::Token![<]>()?;
        let ty: Type = input.parse()?;
        input.parse::<syn::Token![>]>()?;
        let body;
        syn::braced!(body in input);
        let mut rules = IndexMap::new();

        while !body.is_empty() {
            let attrs = body.call(syn::Attribute::parse_outer)?;
            let vis: syn::Visibility = body.parse()?;
            let name = body.call(Ident::parse_any)?;
            let generics = Generics::parse(&body)?;
            let mut fields = Fields::Unit;
            if body.peek(syn::token::Brace) {
                fields = Fields::Structured(body.parse()?);
            }
            body.parse::<syn::Token![->]>()?;
            let ty = body.parse::<Type>()?;
            let mut func = MapFunc::Empty;
            if body.peek(kw::from) {
                body.parse::<kw::from>()?;
                let parens;
                syn::parenthesized!(parens in body);
                func = MapFunc::From(parens.parse::<syn::Expr>()?);
            } else if body.peek(kw::try_from) {
                body.parse::<kw::try_from>()?;
                let parens;
                syn::parenthesized!(parens in body);
                func = MapFunc::TryFrom(parens.parse::<syn::Expr>()?);
            }
            let mut where_clause = None;
            if body.peek(syn::Token![where]) {
                where_clause = Some(body.parse::<syn::WhereClause>()?);
            }
            body.parse::<syn::Token![=]>()?;
            let definition = body.parse::<RuleGroup>()?;
            let end = body.parse::<syn::Token![;]>()?;
            let mut span = vis.span();
            if let Some(joined) = span.join(end.span) {
                span = joined;
            }

            if let Some(
                RuleBody { span: dupe_span, .. }
            ) = rules.insert(name,
                RuleBody { vis, attrs, generics, fields, ty, func, where_clause, span, group: definition }
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
    options: Punctuated<RulePath, syn::Token![:]>,
}

impl Parse for RuleGroup {
    fn parse(input: ParseStream) -> syn::Result<Self> {
        Punctuated::<RulePath, syn::Token![:]>::parse_separated_nonempty(input).map(|options| Self { 
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
enum MapFunc {
    Empty,
    From(Expr),
    TryFrom(Expr)
}

#[derive(Debug, Clone)]
struct RuleBody {
    vis: syn::Visibility,
    attrs: Vec<syn::Attribute>,
    generics: Generics,
    fields: Fields,
    ty: Type,
    func: MapFunc,
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
        let silent = input.peek(syn::Token![_]);
        if silent { input.parse::<syn::Token![_]>()?; }
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
    elements: Punctuated<ElementTy, syn::Token![,]>,
}

impl Parse for RulePath {
    fn parse(input: ParseStream) -> syn::Result<Self> {
        Ok(Self {
            elements: Punctuated::<ElementTy, syn::Token![,]>::parse_separated_nonempty(input)?
        })
    }
}

impl RuleBody {
    #[allow(clippy::too_many_lines)]
    fn tokenize(self, name: &Ident, rule_ty: &Type) -> Vec<Stmt> {
        let cr8 = cr8_name();

        let Self { vis, attrs, mut generics, fields, ty, func, where_clause, span, group } = self;
        let infer = Type::Infer(TypeInfer { underscore_token: Default::default() });

        let tys = match &ty {
            t @ Type::Tuple(tup) if tup.elems.is_empty() => vec![t],
            Type::Tuple(tup) => tup.elems.iter().collect(),
            other => vec![other]
        }.into_iter();

        let mut impl_generics = generics.clone();
        let rule_generics = impl_generics.clone();
        if !impl_generics.params.iter().filter_map(|param| {
            let GenericParam::Lifetime(p) = param else { return None; };
            Some(&p.lifetime)
        }).any(|lt| lt.ident == "input") {
            impl_generics.params.push(GenericParam::Lifetime(
                LifetimeParam::new(Lifetime::new("'input", name.span()))
            ));
        }
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

            let return_expr: Expr = match &func {
                MapFunc::Empty =>
                    syn::parse_quote_spanned!(span=> Ok((#(#variable_names),*))),
                MapFunc::From(func) =>
                    syn::parse_quote_spanned!(span=> Ok((#func)(#(#variable_names),*))),
                MapFunc::TryFrom(func) => 
                    syn::parse_quote_spanned!(
                        span=> 
                        (#func)(#(#variable_names),*)
                            .map_err(|err| {
                                (*input, *index) = __before;
                                #cr8::ParseError::new(
                                    Some(#cr8::Box::new(err)),
                                    rule.name(),
                                    *index
                                )
                            }
                        )
                    )                
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
                    return Err(#cr8::ParseError::new(
                        Some(#cr8::Box::new(err)),
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
                    let first_ty = if let MapFunc::Empty = func {
                        tys.next().unwrap_or_else(||
                            Diagnostic::spanned(ty.span(), Level::Error, "returned type count does not match options".into())
                                .abort()
                        )
                    } else { &infer };
                    if min_options == 0 {
                        syn::parse_quote_spanned!(first.span()=> let arg_0: #first_ty = Some(first);)
                    } else {
                        syn::parse_quote_spanned!(first.span()=> let arg_0: #first_ty = first;)
                    }
                }
            }).into_iter();

            let take_count = min_options.saturating_sub(usize::from(!first.silent));
            for el in (&mut iter).take(take_count) {
                let opt_ty = if let MapFunc::Empty = func {
                    tys.next().unwrap_or_else(||
                        Diagnostic::spanned(ty.span(), Level::Error, "returned type count does not match options".into())
                            .abort()
                    )
                } else { &infer };
                if el.silent {
                    next_args.extend::<Vec<Stmt>>(syn::parse_quote_spanned!(el.span()=>
                        let rule = { #el };
                        if let Err(err) = #cr8::Rule::<'input, #rule_ty>::parse_at(&rule, input, index) {
                            #fail_condition
                        };
                    ));
                    continue;
                }
                let Some(name) = names.next() else { break };
                next_args.extend::<Vec<Stmt>>(syn::parse_quote_spanned!(el.span()=>
                    let rule = { #el };
                    let #name: #opt_ty = match #cr8::Rule::<'input, #rule_ty>::parse_at(&rule, input, index) {
                        Ok(val) => val,
                        Err(err) => #fail_condition
                    };
                ));
            }
            for el in &mut iter {
                if el.silent {
                    next_args.extend::<Vec<Stmt>>(syn::parse_quote_spanned!(el.span()=>
                        let rule = { #el };
                        if let Err(err) = #cr8::Rule::<'input, #rule_ty>::parse_at(&rule, input, index) {
                            #fail_condition
                        };
                    ));
                    continue;
                }
                let Some(name) = names.next() else { break };
                next_args.extend::<Vec<Stmt>>(syn::parse_quote_spanned!(el.span()=>
                    let rule = { #el };
                    let #name = match #cr8::Rule::<'input, #rule_ty>::parse_at(&rule, input, index) {
                        Ok(val) => Some(val),
                        Err(err) => #fail_condition
                    };
                ));
            }
            
            element_defs.extend::<Vec<Stmt>>(syn::parse_quote_spanned!(first.span()=> 'b: {
                let rule = { #first };
                match #cr8::Rule::<'input, #rule_ty>::parse_at(&rule, input, index) {
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

        syn::parse_quote_spanned!(self.span=>
            #(#attrs)*
            #vis struct #name #rule_generics #where_clause #fields

            impl #rule_generics #cr8::NamedRule for #name #generics #where_clause {
                fn name(&self) -> Option<&'static str> { Some(stringify!(#name)) }
            }

            impl #impl_generics #cr8::Rule<'input, #rule_ty> for #name #generics #where_clause {
                type Output = #ty;

                #[allow(unused_variables, unreachable_code, unused_labels, unused_parens)]
                fn parse_at<'cursor, 'this, 'index>(&'this self, input: &'cursor mut &'input #rule_ty, index: &'index mut usize)
                    -> Result<Self::Output, #cr8::ParseError>
                    where 'input : 'this
                {
                    #[allow(unused)]
                    let __before = (*input, *index);
                    #(#optional_variable_defs)*

                    #(#element_defs)*

                    Err(#cr8::ParseError::new(Some(#cr8::Box::new(#cr8::errors::ExhaustedInput)), self.name(), *index))
                }
            }
        )
    }
}

#[proc_macro_derive(NamedRule)]
pub fn derive_named(input: TokenStream) -> TokenStream {
    use syn::Data;

    let cr8 = cr8_name();

    let input = parse_macro_input!(input as syn::DeriveInput);

    let name = input.ident;
    let (impl_generics, ty_generics, where_clause) = input.generics.split_for_impl();
    let expanded = match &input.data {
        Data::Struct(_) | Data::Union(_) => quote! {
            #[automatically_derived]
            impl #impl_generics #cr8::NamedRule for #name #ty_generics #where_clause {
                #[inline]
                fn name(&self) -> Option<&'static str> {
                    Some(stringify!(#name))
                }
            }
        },
        Data::Enum(data_enum) => {
            let variants = &data_enum.variants;
            let variant_pats = variants.iter().map(|variant| -> syn::Pat {
                let name = &variant.ident;
                match variant.fields {
                    syn::Fields::Unit => 
                        syn::Pat::Path(syn::parse_quote!(Self::#name)),
                    syn::Fields::Named(_) => 
                        syn::Pat::Struct(syn::PatStruct {
                            attrs: vec![],
                            qself: None,
                            path: syn::parse_quote!(Self::#name),
                            brace_token: Default::default(),
                            fields: Punctuated::new(),
                            rest: Some(syn::PatRest { attrs: vec![], dot2_token: Default::default(), })
                        }),
                    syn::Fields::Unnamed(_) => 
                        syn::Pat::TupleStruct(syn::PatTupleStruct {
                            attrs: vec![],
                            qself: None,
                            path: syn::parse_quote!(Self::#name),
                            paren_token: Default::default(),
                            elems: [syn::Pat::Rest(syn::PatRest { attrs: vec![], dot2_token: Default::default(), })]
                                    .into_iter().collect()
                        })

                }
            });
            let field_names = variants.iter()
                .map(|variant| format!("{name}::{}", variant.ident));
            
            quote! {
                #[automatically_derived]
                impl #impl_generics #cr8::NamedRule for #name #ty_generics #where_clause  {
                    #[inline]
                    fn name(&self) -> Option<&'static str> {
                        Some(match &self {
                            #(#variant_pats => #field_names),*
                        })
                    }
                }
            }
        }
    };

    TokenStream::from(expanded)
}

#[proc_macro]
#[proc_macro_error::proc_macro_error]
pub fn define(input: TokenStream) -> TokenStream {
    let Grammar {
        attrs, vis, ident, ty, rules, ..
    } = parse_macro_input!(input as Grammar);
    let cr8 = cr8_name();

    let rules = rules.iter().map(|(name, body)| body.clone().tokenize(name, &ty));

    quote!(
        #( #attrs )*
        #[allow(non_snake_case)]
        #vis mod #ident {
            #![allow(unused_imports)]
            #![allow(clippy::double_parens)]
            use super::*;
            use #cr8::NamedRule as _;
            #(#(#rules)*)*
        }
    ).into()
}