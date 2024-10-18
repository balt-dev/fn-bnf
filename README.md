
# fn_bnf

This crate contains a `no_std` compatible, low-allocation parsing grammar generator
that uses a BNF-like syntax with the `define!` macro to allow for
using arbitrary Rust items as grammar rules, 
and for parsing both `str`s and any `[T]` (for example, `[u8]` or `[Token]`).