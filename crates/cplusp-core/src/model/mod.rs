//! The translator from the C++ subset to Dafny, decisions 0056, 0057 and 0058.
//!
//! The shell hands this module the compiler's tree of the functions of one file as plain data, and gets a model of each back. Each
//! rule of the translation is a spec function here, and each exec function is proved to compute exactly its spec. The proofs say:
//!
//! - `translate_unit` and `translate_function`: the result is the spec model, `spec_unit` and `spec_function`.
//! - `translate_file`: the models of `translate_unit`, where no method writes a local back through its interface when an interface of
//!   the file has no final class over it, decision 0217, no call in a method can come back to it through an override of its callee
//!   on a path of any length, `lemma_safe_calls`, decision 0218, and each key keeps its method.
//! - a node that the translator does not know is refused, never skipped: `lemma_unknown_is_refused`.
//! - a translated body has one Dafny statement for each C++ statement: `lemma_statements_kept`.
//! - each call in a method names a function that has a method in the model: `lemma_calls_resolve`.
//! - `parse_contract`: it ends, it reads every token or refuses the line, and an expression it gives holds no unknown node.
//! - an upcast holds only with a check of each virtual function of the interface: `lemma_each_virtual_function_is_checked`.
//! - the pass of globals leaves no reads line that names a global: `lemma_globalize_consumes_reads`.
//! - when an interface of the file has no final class over it, the upcasts give a refusal: `lemma_unbacked`, decision 0220.
//!
//! The predicates of `properties.rs`, such as `has_method` and `calls_resolve`, carry no `spec_` prefix, since no exec function
//! mirrors them.
//!
//! A Dafny expression has no call, so a call in a method stands alone by the shape of the types.
//! The lists are cons lists, so that each rule and each proof is one structural recursion.
//! Names, keys of functions, kinds of construct and lines are numbers. The shell keeps the table of names and prints the text.

mod calls;
mod code;
mod cpp_side;
mod dafny_side;
mod dtor;
mod globals;
mod lists;
mod parser;
mod properties;
mod rules;
mod statics;
mod virtuals;
mod writes;

pub use calls::*;
pub use code::*;
pub use cpp_side::*;
pub use dafny_side::*;
pub use dtor::*;
pub use globals::*;
pub use lists::*;
pub use parser::*;
#[allow(unused_imports)]
pub use properties::*;
pub use rules::*;
pub use statics::*;
pub use virtuals::*;
pub use writes::*;
