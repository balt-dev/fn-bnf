
use fn_bnf_macro::*;

define! {
    pub(crate) grammar Grammar<str> {
        <hello> = *[..1]"world", (one, two);
        <a> = [0..] "foo";
    }
}
