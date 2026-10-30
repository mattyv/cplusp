//! The shell side of the translator, decisions 0056, 0057 and 0124. It reads the plugin's lines of JSON, numbers the names, hands the core the
//! bytes of each contract line and its tables, and prints the Dafny text of what the core gives back. Every rule of the translation is
//! in `cplusp_core`. Nothing here decides what is allowed.

use std::collections::HashMap;
use std::fmt::Write;

use anyhow::{Context, Result};
use cplusp_core::companion::CompanionRefusal;
use cplusp_core::contract::{LexKind, NumberFault};
use cplusp_core::model::{
    globalize, parse_contract, translate_overrides, translate_file, translate_structs, Args, BinOp, CastKind, CondKind, Conds, DArgs, DConds, DExpr, DOverride, DParams, DPre, DStmt, DStmts, DTy, DUpcast, Expr, Extent, Fns,
    Function, List, Members, Method, Model, Names as CNames, Obj, Objs, Params, Refusal, Scalar, Stmt, Stmts, Structs, Tok, Ty,
};
use serde::Deserialize;

// ------------------------------------------------------------------ the plugin's lines, in the core's shape with names as text

#[derive(Deserialize)]
enum JScalar {
    I32,
    I64,
    U8,
    U32,
    U64,
    Bool,
    Struct(String),
    /// A unique_ptr of a struct or an interface, as the element of a sequence, decision 0170.
    Own(String),
}

#[derive(Deserialize)]
enum JTy {
    /// `double`, decision 0150.
    F64,
    I32,
    I64,
    U8,
    U32,
    U64,
    I8,
    I16,
    U16,
    Bool,
    Seq(JScalar, Option<u64>),
    Struct(String),
    /// A parameter of type `T&`, decision 0108.
    Mut(JScalar),
    /// A parameter of type `std::vector<T>&` that the function writes, decision 0145.
    MutSeq(JScalar),
    /// `this` of a pure virtual function of an interface, and a parameter `const B&` of one, by the key of its struct, decision 0165.
    Iface(String),
    IfaceRef(String),
    /// `this` of a pure virtual function that is not const, decision 0169.
    IfaceMut(String),
    /// A local `std::vector<T>` that the function owns, decision 0160.
    Vec(JScalar),
    /// An enum class of the file by its key, decision 0109.
    Enum(String),
    Opt(JScalar),
    /// A `std::variant` of two different element types, decision 0202.
    Variant(JScalar, JScalar),
    /// A pointer to const that is a parameter, decision 0141.
    Ptr(JScalar),
    /// A unique_ptr that the code only reads, decision 0142.
    Own(JScalar),
    This(String),
    ThisMut(String),
    Void,
    Other(String),
}

#[derive(Deserialize)]
enum JOp {
    Add,
    Sub,
    Mul,
    Div,
    Rem,
    Lt,
    Le,
    Gt,
    Ge,
    Eq,
    Ne,
    And,
    Or,
    BitAnd,
    BitOr,
}

#[derive(Deserialize)]
enum JCast {
    Read,
    NoOp,
    Construct,
    Integral(JTy, JTy),
    /// A final class to its interface, by their keys, decision 0166.
    Upcast(String, String),
    Other(String),
}

#[derive(Deserialize)]
enum JExpr {
    Lit(u64, JTy),
    Bool(bool),
    Var(String, JTy),
    /// `std::move(x)` of a local or a parameter of type unique_ptr, by the name and the type of `x`, decision 0171.
    Move(String, JTy),
    Bin(JOp, Box<JExpr>, Box<JExpr>),
    Divide(JOp, Box<JExpr>, Box<JExpr>, JTy),
    Shr(Box<JExpr>, Box<JExpr>, JTy),
    /// `x++`, `x--`, `++x` or `--x` inside an expression: the name, its type, whether it adds, and whether it is a prefix, decision 0177.
    Step(String, JTy, bool, bool),
    /// `a & b` or `a | b` of unsigned operands, by the type of the result, decision 0175.
    Bits(JOp, Box<JExpr>, Box<JExpr>, JTy),
    /// `return {a, b, c};` of a std::array result, decision 0175.
    List(Vec<JExpr>),
    /// An enumerator by the key of its enum and its place, decision 0109.
    Enumerator(String, u32),
    Not(Box<JExpr>),
    Neg(Box<JExpr>),
    Cast(JCast, Box<JExpr>),
    Paren(Box<JExpr>),
    Brace(Box<JExpr>),
    Size(Box<JExpr>),
    /// `v.back()` of a vector, decision 0191.
    Back(Box<JExpr>),
    Empty(Box<JExpr>),
    /// A local vector with no initial value, decision 0170.
    EmptyVec,
    /// `v(n, x)`, the start value of a local vector, by the count and the value, decision 0185.
    Fill(Box<JExpr>, Box<JExpr>),
    Subspan(Box<JExpr>, Box<JExpr>),
    Copy(Box<JExpr>, JTy, JTy),
    Field(Box<JExpr>, String),
    HasValue(Box<JExpr>),
    Value(Box<JExpr>),
    /// `std::holds_alternative<T>(v)` and `std::get<T>(v)`, by the type `T`, decision 0202.
    Holds(JTy, Box<JExpr>),
    GetAlt(JTy, Box<JExpr>),
    Nullopt,
    Wrap(Box<JExpr>),
    Construct(String, Vec<JExpr>),
    Index(Box<JExpr>, Box<JExpr>),
    Cond(Box<JExpr>, Box<JExpr>, Box<JExpr>),
    /// A literal of type double, `d / 10^k`, decision 0150.
    RealLit(u64, u32),
    /// A literal of type double, `m / q` with `q` a power of two, decision 0158.
    Ratio(u64, u64),
    /// `std::count_if(v.begin(), v.end(), f)` with a lambda: the sequence, the parameter, its type and the test, decision 0149.
    CountIf(Box<JExpr>, String, JTy, Box<JExpr>),
    Call(String, String, Vec<JExpr>, u32),
    Unknown(String, u32),
}

#[derive(Deserialize)]
enum JStmt {
    Return(JExpr, u32),
    If(JExpr, Vec<JStmt>, Vec<JStmt>, u32),
    Local(String, JTy, JExpr, u32),
    Assign(String, JExpr, u32),
    Step(String, JTy, bool, u32),
    SetField(String, JExpr, u32),
    /// `v[i] = e` where `v` is a vector by reference, decision 0145.
    SetIndex(String, JExpr, JExpr, u32),
    /// `f[i] = e` where `f` is a vector or array field of the object, decision 0187.
    SetFieldAt(String, JExpr, JExpr, u32),
    /// `v.push_back(e)` where `v` is a vector by reference, decision 0148.
    PushBack(String, JExpr, u32),
    /// `f.push_back(e)` where `f` is a vector field of the object, decision 0191.
    PushField(String, JExpr, u32),
    /// `f.pop_back()` where `f` is a vector field of the object, decision 0191.
    PopField(String, u32),
    /// `std::sort(v.begin(), v.end())`, decision 0161.
    Sort(String, u32),
    /// `std::sort(v.begin(), v.end(), [captures](T a, T b) { return e; })`: the vector, the two parameters, their type, the test and the line, decision 0162.
    SortBy(String, String, String, JTy, JExpr, u32),
    /// `p.f = e` where `p` is a reference parameter, decision 0108.
    SetRefField(String, String, JExpr, u32),
    /// `n->f = e` where `n` is a local `std::unique_ptr` of a plain struct, decision 0186.
    SetOwnField(String, String, JExpr, u32),
    /// `f->g = e` where `f` is a `std::unique_ptr` field of the object, decision 0197.
    SetThroughField(String, String, JExpr, u32),
    /// A switch over an enum, decision 0109: its condition, the key of the enum, the cases as (place of the enumerator, statements), and the line.
    Switch(JExpr, String, Vec<(u32, Vec<JStmt>)>, u32),
    Call(String, String, Vec<JExpr>, u32),
    Exit(u32),
    /// A bare block `{ ... }`: its statements and its line, decision 0178.
    Block(Vec<JStmt>, u32),
    /// A `//@ assert` or `//@ apply` line in the body, decision 0099.
    Assert(JCond),
    Apply(JCond),
    While(JExpr, Vec<JCond>, Vec<JStmt>, u32),
    For(Box<JStmt>, JExpr, Box<JStmt>, Vec<JCond>, Vec<JStmt>, u32),
    /// A range-for over a sequence parameter, decision 0143: the loop variable, its type, the sequence, the loop's lines, the body and the line.
    RangeFor(String, JTy, JExpr, Vec<JCond>, Vec<JStmt>, u32),
    Unknown(String, u32),
}

#[derive(Deserialize)]
struct JCond {
    file: String,
    kind: String,
    line: u32,
    text: String,
    params: Vec<String>,
}

/// A line of the plugin: a function, or a `//@` line that no function claimed.
#[derive(Deserialize)]
#[serde(untagged)]
enum Item {
    Orphan {
        orphan: u32,
        file: String,
        /// The word of the line, when it starts with `//@`.
        #[serde(default)]
        word: String,
    },
    /// A named constant of the file, decision 0106: its name and its value as decimal text.
    Constant {
        constant: String,
        value: String,
    },
    /// A named double constant of the file, decision 0158: its name, and its sign, `m` and `q` for the value `m / q`.
    Real {
        constant: String,
        real: (bool, u64, u64),
    },
    /// A mutable global or static data member that the file defines, in the order of the definitions, decision 0173: its name and its type.
    Global {
        global: String,
        ty: JTy,
    },
    /// An enum class that is its underlying integer, decision 0175: its plain name and its enumerators with their values.
    Valued {
        valued: String,
        values: Vec<(String, u64)>,
    },
    Enum(JEnum),
    Struct(JStruct),
    Function(JFunction),
}

/// An enum class of the file, decision 0109.
#[derive(Deserialize)]
struct JEnum {
    #[serde(rename = "enum")]
    key: String,
    name: String,
    file: String,
    line: u32,
    enumerators: Vec<String>,
}

/// A plain struct of the file, decision 0073.
#[derive(Deserialize)]
struct JStruct {
    #[serde(rename = "struct")]
    key: String,
    name: String,
    file: String,
    line: u32,
    fields: Vec<(String, JTy)>,
    /// The member functions that are written as functions, as (name, key), decision 0090.
    members: Vec<(String, String)>,
    /// The keys of the interfaces that a class derives from, and whether it is final, decision 0165.
    #[serde(default)]
    bases: Vec<String>,
    #[serde(default, rename = "final")]
    is_final: bool,
    /// An interface: a class with no field whose members are pure virtual, decision 0165.
    #[serde(default)]
    interface: bool,
    /// The name of the class in C++ with its namespaces, for the Axiom line of an interface, decision 0166.
    #[serde(default)]
    qualified: String,
    /// The type arguments of an instance of a class template, decision 0188.
    #[serde(default)]
    of: Vec<JTy>,
    /// The Dafny name without `S_`: the name, and for an instance `'of'` and the Dafny type of each argument. Set after the lines are read, decision 0188.
    #[serde(skip)]
    full: String,
}

#[derive(Deserialize)]
struct JFunction {
    key: String,
    name: String,
    file: String,
    line: u32,
    params: Vec<(String, JTy)>,
    ret: JTy,
    /// The reason of the marker `CPLUSP_TRUSTED`, and the file and line of the declaration that has it, when the function is trusted,
    /// decisions 0102 and 0103.
    #[serde(default)]
    trusted: Option<(String, String, u32)>,
    /// A pure virtual function of an interface: the contract stands with no body, as for a trusted function, decision 0165.
    #[serde(default)]
    interface: bool,
    /// The constants of the file that C++ does not find from the function, decision 0107. They hide no constant from `shadow`, they join it.
    #[serde(default)]
    hidden: Vec<String>,
    /// The qualified name of the class when the function is a static member function, decision 0174. Its `name` is the qualified name of the function.
    #[serde(default, rename = "static")]
    class: Option<String>,
    /// The type arguments of an instance of a function template, decision 0180.
    #[serde(default)]
    of: Vec<JTy>,
    conds: Vec<JCond>,
    body: Vec<JStmt>,
}

// ------------------------------------------------------------------ the table of names

/// Names, kinds and words get a number in the order they first appear. The core compares numbers, and this table prints them.
/// A place is a pair of a file and a line, and it gets a number the same way. The core never computes with a line, so it gets places.
/// `file` is the file of the function that is being converted, and `here` makes a place in it.
// ponytail: a linear search. A file has dozens of names and places. Upgrade: a hash map.
#[derive(Default)]
struct Names {
    words: Vec<String>,
    places: Vec<(String, u32)>,
    /// The word and text of each contract line by its place, for the report of the prover.
    contracts: HashMap<u32, (String, String)>,
    /// The Dafny name of each struct by the id of its key.
    datatypes: HashMap<u32, String>,
    file: String,
    /// The number of the first temporary of the `Pre` that is being printed, decision 0104. `Temp(t)` prints as temporary `temp_base + t`.
    /// `None` outside a `Pre`.
    temp_base: std::cell::Cell<Option<u32>>,
    /// Whether the printer wrote a call of `fadd` to `fdiv`, so a verdict rests on the rounding axiom, decision 0154.
    rounds: std::cell::Cell<bool>,
    /// Whether the printer wrote a name of the module `Double`: `fadd` to `fdiv`, `abs`, `EPS`, `ETA` or `MAX`, so the module is in the model.
    double: std::cell::Cell<bool>,
    /// Whether the printer wrote `fint`, so a verdict rests on the exact-integer axiom, decision 0159.
    exact: std::cell::Cell<bool>,
    /// Whether the printer wrote `StdSort`, so a verdict rests on its contract, decision 0161.
    sorted: std::cell::Cell<bool>,
    /// The plain name of each class of the table of structs by the id of its key, and of each function by the id of its key, for the sentences of decision 0165.
    class_names: HashMap<u32, String>,
    /// The name of each interface by the id of its key, as its Axiom line names it, decision 0166: the plain name, or the qualified name when two structs share it.
    interface_names: HashMap<u32, String>,
    fn_names: HashMap<u32, String>,
    /// The id of the key of the class of `this` of each member function, by the id of its key, for the sentence of decision 0218.
    fn_classes: HashMap<u32, u32>,
    /// The functions that the companion file declares. Empty when there is no file or the scan refused it, decision 0079.
    declared: Vec<String>,
    /// The lemmas that the companion file declares, apart from the functions, decision 0099.
    lemmas: Vec<String>,
    /// The sentence of a body line that the core refuses as `Syntax`, by the place of the line.
    said: HashMap<u32, String>,
    /// The first call to an undeclared name in a contract line, by the place of the line.
    /// With 0 when the name is no function of the companion file, 1 when it is a function of the file and of the companion file, decision 0176, and 2 when it is a
    /// static member function that two functions share, decision 0215.
    bad_calls: HashMap<u32, (String, u8)>,
    /// The lines of `bad_calls` whose name is a virtual function of the struct that shares its name with another, decision 0217.
    shared_calls: std::collections::HashSet<u32>,
    /// The plain names of the free functions that the table of structs lists under the file, decision 0176. A contract calls them.
    file_fns: Vec<String>,
    /// The member names of each struct by its key, for the contracts of its member functions, decision 0090.
    members: HashMap<String, Vec<String>>,
    /// The member names of the struct of `this` in the function that is being converted. Empty for any other function.
    this_members: Vec<String>,
    /// The Dafny name of the function of each pure member function by the id of its key: the name of its method, and `'`.
    functions: HashMap<u32, String>,
    /// The names of the parameters and of the fields of the object that are of a struct type, in the function that is being converted. A call of one in a
    /// contract may be a call of its `operator()`, and the core decides, decision 0098.
    functors: Vec<String>,
    /// The names of the fields of a struct type, by the key of each struct.
    struct_fields: HashMap<String, Vec<String>>,
    /// The named constants of the file, as (name, value), decision 0106. A contract reads such a name as its value.
    constants: Vec<(String, i128)>,
    /// The named double constants of the file as (name, negative, m, q) for the value `m / q`, decision 0158.
    reals: Vec<(String, bool, u64, u64)>,
    /// The enums of the file as (plain name, id of key, enumerators), for `Kind::Small` in a contract, decision 0109.
    enums: Vec<(String, u32, Vec<String>)>,
    /// The names of the parameters and locals of the function that is being converted. They hide a constant of the same name.
    shadow: Vec<String>,
    /// The valued enums of the file as (plain name, enumerators with their values), decision 0175. A contract reads `Flag::Write` as its value.
    valued: Vec<(String, Vec<(String, u64)>)>,
    /// The names of the globals of the file. A contract may spell a static data member `Registry::last_id`, decision 0173.
    globals: Vec<String>,
    /// The qualified names of the static member functions of the file, and the class of the function that is being converted, decision 0174. A bare call
    /// in the contract of a static member function names a static of its class.
    statics: Vec<String>,
    class: Option<String>,
    /// The number of range-fors converted so far, for the name of an index that no line names, decision 0144.
    ranges: u32,
}

impl Names {
    fn id(&mut self, s: &str) -> u32 {
        let at = self.words.iter().position(|n| n == s).unwrap_or_else(|| {
            self.words.push(s.to_string());
            self.words.len() - 1
        });
        at as u32
    }
    /// The id of a word that the table has, or none. It adds nothing.
    fn find(&self, s: &str) -> Option<u32> {
        self.words.iter().position(|n| n == s).map(|at| at as u32)
    }
    fn text(&self, id: u32) -> &str {
        &self.words[id as usize]
    }
    fn place(&mut self, file: &str, line: u32) -> u32 {
        let at = self.places.iter().position(|(f, l)| f == file && *l == line).unwrap_or_else(|| {
            self.places.push((file.to_string(), line));
            self.places.len() - 1
        });
        at as u32
    }
    fn here(&mut self, line: u32) -> u32 {
        let file = self.file.clone();
        self.place(&file, line)
    }
}

// ------------------------------------------------------------------ from JSON to the core's types

fn scalar(s: JScalar, names: &mut Names) -> Scalar {
    match s {
        JScalar::I32 => Scalar::I32,
        JScalar::I64 => Scalar::I64,
        JScalar::U8 => Scalar::U8,
        JScalar::U32 => Scalar::U32,
        JScalar::U64 => Scalar::U64,
        JScalar::Bool => Scalar::Bool,
        JScalar::Struct(k) => Scalar::Struct(names.id(&k)),
        JScalar::Own(k) => Scalar::Own(names.id(&k)),
    }
}

fn ty(t: JTy, names: &mut Names) -> Ty {
    match t {
        JTy::I32 => Ty::I32,
        JTy::I64 => Ty::I64,
        JTy::U8 => Ty::U8,
        JTy::U32 => Ty::U32,
        JTy::U64 => Ty::U64,
        JTy::F64 => Ty::F64,
        JTy::I8 => Ty::I8,
        JTy::I16 => Ty::I16,
        JTy::U16 => Ty::U16,
        JTy::Bool => Ty::Bool,
        JTy::Seq(s, extent) => Ty::Seq(scalar(s, names), extent.map_or(Extent::Dynamic, Extent::Fixed)),
        JTy::Opt(s) => Ty::Opt(scalar(s, names)),
        JTy::Variant(a, b) => Ty::Variant(scalar(a, names), scalar(b, names)),
        JTy::Ptr(s) => Ty::Ptr(scalar(s, names)),
        JTy::Own(s) => Ty::Own(scalar(s, names)),
        JTy::Struct(k) => Ty::Struct(names.id(&k)),
        JTy::Mut(s) => Ty::Mut(scalar(s, names)),
        JTy::MutSeq(s) => Ty::MutSeq(scalar(s, names)),
        JTy::Iface(k) => Ty::Iface(names.id(&k)),
        JTy::IfaceRef(k) => Ty::IfaceRef(names.id(&k)),
        JTy::IfaceMut(k) => Ty::IfaceMut(names.id(&k)),
        JTy::Vec(s) => Ty::Vec(scalar(s, names)),
        JTy::Enum(k) => Ty::Enum(names.id(&k)),
        JTy::This(k) => Ty::This(names.id(&k)),
        JTy::ThisMut(k) => Ty::ThisMut(names.id(&k)),
        JTy::Void => Ty::Void,
        JTy::Other(s) => Ty::Other(names.id(&s)),
    }
}

fn op(o: JOp) -> BinOp {
    match o {
        JOp::Add => BinOp::Add,
        JOp::Sub => BinOp::Sub,
        JOp::Mul => BinOp::Mul,
        JOp::Div => BinOp::Div,
        JOp::Rem => BinOp::Rem,
        JOp::Lt => BinOp::Lt,
        JOp::Le => BinOp::Le,
        JOp::Gt => BinOp::Gt,
        JOp::Ge => BinOp::Ge,
        JOp::Eq => BinOp::Eq,
        JOp::Ne => BinOp::Ne,
        JOp::And => BinOp::And,
        JOp::Or => BinOp::Or,
        JOp::BitAnd => BinOp::BitAnd,
        JOp::BitOr => BinOp::BitOr,
    }
}

fn expr(e: JExpr, names: &mut Names) -> Expr {
    match e {
        JExpr::Lit(n, t) => Expr::Lit(n, ty(t, names)),
        JExpr::Bool(b) => Expr::Bool(b),
        JExpr::RealLit(d, k) => Expr::RealLit(d, k),
        JExpr::Ratio(m, q) => Expr::Ratio(m, q),
        JExpr::Var(v, t) => Expr::Var(names.id(&v), ty(t, names)),
        JExpr::Move(v, t) => Expr::Move(names.id(&v), ty(t, names)),
        JExpr::Bin(o, a, b) => Expr::Bin(op(o), Box::new(expr(*a, names)), Box::new(expr(*b, names))),
        JExpr::Divide(o, a, b, t) => Expr::Divide(op(o), Box::new(expr(*a, names)), Box::new(expr(*b, names)), ty(t, names)),
        JExpr::Shr(a, b, t) => Expr::Shr(Box::new(expr(*a, names)), Box::new(expr(*b, names)), ty(t, names)),
        JExpr::Step(v, t, up, prefix) => Expr::Step(names.id(&v), ty(t, names), up, prefix),
        JExpr::Bits(o, a, b, t) => Expr::Bits(op(o), Box::new(expr(*a, names)), Box::new(expr(*b, names)), ty(t, names)),
        JExpr::List(args) => {
            let args: Vec<Expr> = args.into_iter().map(|a| expr(a, names)).collect();
            Expr::List(Box::new(args.into_iter().rev().fold(Args::Nil, |rest, a| Args::Cons(Box::new(a), Box::new(rest)))))
        }
        JExpr::Enumerator(k, i) => Expr::Enumerator(names.id(&k), i),
        JExpr::Not(a) => Expr::Not(Box::new(expr(*a, names))),
        JExpr::Neg(a) => Expr::Neg(Box::new(expr(*a, names))),
        JExpr::Cast(k, a) => {
            let kind = match k {
                JCast::Read => CastKind::Read,
                JCast::NoOp => CastKind::NoOp,
                JCast::Construct => CastKind::Construct,
                JCast::Integral(from, to) => CastKind::Integral(ty(from, names), ty(to, names)),
                JCast::Upcast(d, b) => CastKind::Upcast(names.id(&d), names.id(&b)),
                JCast::Other(s) => CastKind::Other(names.id(&s)),
            };
            Expr::Cast(kind, Box::new(expr(*a, names)))
        }
        JExpr::Paren(a) => Expr::Paren(Box::new(expr(*a, names))),
        JExpr::Brace(a) => Expr::Brace(Box::new(expr(*a, names))),
        JExpr::Size(a) => Expr::Size(Box::new(expr(*a, names))),
        JExpr::Back(a) => Expr::Back(Box::new(expr(*a, names))),
        JExpr::Empty(a) => Expr::Empty(Box::new(expr(*a, names))),
        JExpr::EmptyVec => Expr::EmptyVec,
        JExpr::Fill(n, x) => Expr::Fill(Box::new(expr(*n, names)), Box::new(expr(*x, names))),
        JExpr::Subspan(a, k) => Expr::Subspan(Box::new(expr(*a, names)), Box::new(expr(*k, names))),
        JExpr::Copy(a, from, to) => Expr::Copy(Box::new(expr(*a, names)), ty(from, names), ty(to, names)),
        JExpr::Field(a, f) => Expr::Field(Box::new(expr(*a, names)), names.id(&f)),
        JExpr::HasValue(a) => Expr::HasValue(Box::new(expr(*a, names))),
        JExpr::Value(a) => Expr::Value(Box::new(expr(*a, names))),
        JExpr::Holds(t, a) => Expr::Holds(ty(t, names), Box::new(expr(*a, names))),
        JExpr::GetAlt(t, a) => Expr::GetAlt(ty(t, names), Box::new(expr(*a, names))),
        JExpr::Nullopt => Expr::Nullopt,
        JExpr::Wrap(a) => Expr::Wrap(Box::new(expr(*a, names))),
        JExpr::Construct(k, args) => {
            let args: Vec<Expr> = args.into_iter().map(|a| expr(a, names)).collect();
            let args = args.into_iter().rev().fold(Args::Nil, |rest, a| Args::Cons(Box::new(a), Box::new(rest)));
            Expr::Construct(names.id(&k), Box::new(args))
        }
        JExpr::Index(a, i) => Expr::Index(Box::new(expr(*a, names)), Box::new(expr(*i, names))),
        JExpr::CountIf(v, x, xt, t) => Expr::CountIf(Box::new(expr(*v, names)), names.id(&x), ty(xt, names), Box::new(expr(*t, names))),
        JExpr::Cond(c, a, b) => Expr::Cond(Box::new(expr(*c, names)), Box::new(expr(*a, names)), Box::new(expr(*b, names))),
        JExpr::Call(key, name, args, line) => {
            let args: Vec<Expr> = args.into_iter().map(|a| expr(a, names)).collect();
            let args = args.into_iter().rev().fold(Args::Nil, |rest, a| Args::Cons(Box::new(a), Box::new(rest)));
            Expr::Call(names.id(&key), names.id(&name), Box::new(args), names.here(line))
        }
        JExpr::Unknown(k, line) => Expr::Unknown(names.id(&k), names.here(line)),
    }
}

fn stmt(s: JStmt, names: &mut Names) -> Stmt {
    match s {
        JStmt::Return(e, line) => Stmt::Return(expr(e, names), names.here(line)),
        JStmt::If(c, t, f, line) => Stmt::If(expr(c, names), Box::new(stmts(t, names)), Box::new(stmts(f, names)), names.here(line)),
        JStmt::Local(n, t, e, line) => Stmt::Local(names.id(&n), ty(t, names), expr(e, names), names.here(line)),
        JStmt::Assign(n, e, line) => Stmt::Assign(names.id(&n), expr(e, names), names.here(line)),
        JStmt::Step(n, t, up, line) => Stmt::Step(names.id(&n), ty(t, names), up, names.here(line)),
        JStmt::SetField(f, e, line) => Stmt::SetField(names.id(&f), expr(e, names), names.here(line)),
        JStmt::SetIndex(v, i, e, line) => Stmt::SetIndex(names.id(&v), expr(i, names), expr(e, names), names.here(line)),
        JStmt::SetFieldAt(f, i, e, line) => Stmt::SetFieldAt(names.id(&f), expr(i, names), expr(e, names), names.here(line)),
        JStmt::PushBack(v, e, line) => Stmt::PushBack(names.id(&v), expr(e, names), names.here(line)),
        JStmt::PushField(f, e, line) => Stmt::PushField(names.id(&f), expr(e, names), names.here(line)),
        JStmt::PopField(f, line) => Stmt::PopField(names.id(&f), names.here(line)),
        JStmt::Sort(v, line) => Stmt::Sort(names.id(&v), names.here(line)),
        JStmt::SortBy(v, a, b, t, e, line) => {
            let (v, a, b, t) = (names.id(&v), names.id(&a), names.id(&b), ty(t, names));
            Stmt::SortBy(v, a, b, t, expr(e, names), names.here(line))
        }
        JStmt::Switch(e, k, cases, line) => {
            let place = names.here(line);
            let key = names.id(&k);
            let cases = cases.into_iter().rev().fold(List::Nil, |rest, (i, body)| List::Cons((i, Box::new(stmts(body, names))), Box::new(rest)));
            Stmt::Switch(expr(e, names), key, Box::new(cases), place)
        }
        JStmt::SetRefField(p, f, e, line) => Stmt::SetRefField(names.id(&p), names.id(&f), expr(e, names), names.here(line)),
        JStmt::SetOwnField(n, f, e, line) => Stmt::SetOwnField(names.id(&n), names.id(&f), expr(e, names), names.here(line)),
        JStmt::SetThroughField(f, g, e, line) => Stmt::SetThroughField(names.id(&f), names.id(&g), expr(e, names), names.here(line)),
        JStmt::Call(key, name, args, line) => {
            let args: Vec<Expr> = args.into_iter().map(|a| expr(a, names)).collect();
            let args = args.into_iter().rev().fold(Args::Nil, |rest, a| Args::Cons(Box::new(a), Box::new(rest)));
            Stmt::Call(names.id(&key), names.id(&name), Box::new(args), names.here(line))
        }
        JStmt::Exit(line) => Stmt::Exit(names.here(line)),
        JStmt::Block(body, line) => Stmt::Block(Box::new(stmts(body, names)), names.here(line)),
        JStmt::Assert(c) => body_line(c, false, names),
        JStmt::Apply(c) => body_line(c, true, names),
        JStmt::While(c, cs, body, line) => Stmt::While(expr(c, names), Box::new(conds(cs, names)), Box::new(stmts(body, names)), names.here(line)),
        JStmt::For(init, c, step, cs, body, line) => {
            let init = Box::new(stmt(*init, names));
            let c = expr(c, names);
            Stmt::For(init, c, Box::new(stmt(*step, names)), Box::new(conds(cs, names)), Box::new(stmts(body, names)), names.here(line))
        }
        JStmt::RangeFor(x, t, seq, cs, body, line) => {
            // The index that no index line names. It starts with a digit, so no C++ name is the same, decision 0143. The count of range-fors
            // before it makes it new for each loop, decision 0144.
            names.ranges += 1;
            let fresh = names.id(&format!("{line}_{}_index", names.ranges));
            let (x, t) = (names.id(&x), ty(t, names));
            Stmt::RangeFor(fresh, x, t, expr(seq, names), Box::new(conds(cs, names)), Box::new(stmts(body, names)), names.here(line))
        }
        JStmt::Unknown(k, line) => Stmt::Unknown(names.id(&k), names.here(line)),
    }
}

/// An assert line or an apply line of a body, decision 0099. A line the core cannot take as a fact or a call is a statement that it refuses at the
/// line: `Stmt::Unknown` for a token with no rule, and else `assert result`, which is `Syntax`. `names.said` has the sentence for a `Syntax` of its own.
fn body_line(c: JCond, apply: bool, names: &mut Names) -> Stmt {
    let line = names.place(&c.file, c.line);
    names.contracts.insert(line, (c.kind.clone(), c.text.trim().to_string()));
    // ponytail: a line the core cannot take is `assert result`, which the core refuses as `Syntax` at the line. The ceiling is that this relies on the
    // core refusing `result` in an assert line. Upgrade: a `Stmt::Bad(Refusal)` in the core, like `CondKind::Bad`.
    fn syntax(line: u32, said: Option<String>, names: &mut Names) -> Stmt {
        names.said.extend(said.map(|s| (line, s)));
        Stmt::Assert(Expr::Result, line)
    }
    // A backslash at the end splices the next line into the comment. The line the author wrote is not the one the plugin read.
    if c.text.ends_with('\\') {
        return syntax(line, Some("a contract line that ends in a backslash.".to_string()), names);
    }
    let (head, text) = if apply {
        // `L(a, b)`: a name, then `(`, then the arguments. The name is a lemma of the companion file, and the rest is lexed as a contract.
        let text = c.text.trim_start();
        let end = text.find(|ch: char| !(ch.is_ascii_alphanumeric() || ch == '_')).unwrap_or(text.len());
        let (head, rest) = text.split_at(end);
        let rest = rest.trim_start();
        if head.is_empty() || head.starts_with(|ch: char| ch.is_ascii_digit()) || !rest.starts_with('(') {
            return syntax(line, None, names);
        }
        // `MulBound` is a lemma of the prelude, decision 0167.
        if head != "MulBound" && !names.lemmas.iter().any(|l| l == head) {
            return syntax(line, Some(format!("{head} is no lemma of the companion file.")), names);
        }
        // The call ends at the `)` that closes its `(`. Anything after it is a form the translator cannot read.
        let mut depth = 0usize;
        let close = rest.char_indices().find(|(_, ch)| {
            depth = (depth + usize::from(*ch == '(')).saturating_sub(usize::from(*ch == ')'));
            *ch == ')' && depth == 0
        });
        if close.is_none_or(|(i, _)| !rest[i + 1..].trim().is_empty()) {
            return syntax(line, None, names);
        }
        (Some(head), &rest[1..])
    } else {
        (None, c.text.as_str())
    };
    let mut toks: Vec<Tok> = head.into_iter().flat_map(|h| [Tok::Ident(names.id(h)), Tok::LParen]).collect();
    let lexed = lex(text, line, names);
    if let Some(word) = word_clash(&lexed, &c.params, names) {
        return syntax(line, Some(word_clash_sentence(word)), names);
    }
    toks.extend(fold_names(lexed, names));
    // A call to an undeclared name is refused by `sentence` at this line.
    if names.bad_calls.contains_key(&line) {
        return syntax(line, None, names);
    }
    match (parse_contract(&toks, line), apply) {
        (Ok(Expr::Apply(n, args)), true) => Stmt::Apply(n, args, line),
        (Ok(e), false) => Stmt::Assert(e, line),
        (Err(Refusal::Construct(k, l)), _) => Stmt::Unknown(k, l),
        _ => syntax(line, None, names),
    }
}

/// A cons list from a vector.
fn stmts(v: Vec<JStmt>, names: &mut Names) -> Stmts {
    let items: Vec<Stmt> = v.into_iter().map(|s| stmt(s, names)).collect();
    items.into_iter().rev().fold(List::Nil, |rest, s| List::Cons(Box::new(s), Box::new(rest)))
}

// ------------------------------------------------------------------ the contract lexer

/// Cut the text of a contract line into tokens, decision 0124. The core reads the bytes. The shell gives each name its id and makes the text of each
/// refusal. Any text with no token is `Tok::Unknown`, and the parser refuses the line there.
fn lex(text: &str, line: u32, names: &mut Names) -> Vec<Tok> {
    let bytes = text.as_bytes().to_vec();
    // A name after `->` is a member of the object on the left, as a name after `.` is, decision 0168.
    let mut after_arrow = false;
    // The qualified name that ends before the lexeme, `Tally::` of `Tally::count`, decision 0174.
    let mut chain = String::new();
    let mut after_colons = false;
    cplusp_core::contract::lex_contract(&bytes)
        .into_iter()
        .map(|lexeme| {
            let word = &text[lexeme.start..lexeme.end];
            let member = after_arrow;
            after_arrow = matches!(lexeme.kind, LexKind::Fixed(Tok::Arrow));
            match lexeme.kind {
                LexKind::Name(call) => {
                    chain = if after_colons { format!("{chain}::{word}") } else { word.to_string() };
                    after_colons = false;
                    // A static member function of the file: qualified, or bare in a contract of its class, decision 0174.
                    let static_call = match (&names.class, chain != word) {
                        (_, true) => names.statics.contains(&chain),
                        (Some(class), false) => names.statics.contains(&format!("{class}::{word}")),
                        _ => false,
                    };
                    // A name followed by `(` is a call, and the companion file must declare it. A member name in a member function may be a call of
                    // the member, and the core decides, decision 0090. A member of two virtual functions of one name has the plain name before the `'`, decision 0217.
                    let listed = names.file_fns.iter().any(|d| d == word);
                    if call && !member && !static_call && !listed && !names.declared.iter().any(|d| d == word) && !names.this_members.iter().any(|d| d == word) && !names.functors.iter().any(|d| d == word) {
                        names.bad_calls.entry(line).or_insert_with(|| (word.to_string(), 0));
                    }
                    // A name that two virtual functions of the struct share is no function of a contract. Its members are in the table by the name and the
                    // parameter types, so the sentence is the one of a function that is not pure, decision 0217.
                    if call && !member && !static_call && !names.this_members.iter().any(|d| d == word) && names.this_members.iter().any(|d| plain_member(d) == word) {
                        names.bad_calls.entry(line).or_insert_with(|| (word.to_string(), 0));
                        names.shared_calls.insert(line);
                    }
                    // A name of the file and of the companion file is two functions in a contract, decision 0176.
                    if call && !member && listed && names.declared.iter().any(|d| d == word) {
                        names.bad_calls.entry(line).or_insert_with(|| (word.to_string(), 1));
                    }
                    // A static member function that the table of members leaves out has a name that two functions share, so a contract cannot call it, decision 0215.
                    if call && !member && static_call {
                        let qualified = if chain == word { names.class.as_ref().map(|c| format!("{c}::{word}")).unwrap_or_default() } else { chain.clone() };
                        if !names.members.values().any(|list| list.contains(&qualified)) {
                            names.bad_calls.entry(line).or_insert_with(|| (qualified, 2));
                        }
                    }
                    Tok::Ident(names.id(word))
                }
                LexKind::Field => Tok::Field(names.id(&word[1..])),
                LexKind::Fixed(tok) => {
                    after_colons = tok == Tok::ColonColon && !chain.is_empty();
                    if !after_colons {
                        chain.clear();
                    }
                    // The core lexer cannot intern: the shell gives the three names their ids, decision 0200.
                    match tok {
                        Tok::Size(_) => Tok::Size(names.id("size")),
                        Tok::Empty(_) => Tok::Empty(names.id("empty")),
                        Tok::Back(_) => Tok::Back(names.id("back")),
                        tok => tok,
                    }
                }
                LexKind::Int(value) => Tok::Int(value),
                LexKind::Real(digits, after) => Tok::Real(digits, after),
                LexKind::BadNumber(fault) => {
                    // The number without its digit separators.
                    let number: String = word.chars().filter(|&ch| ch != '\'').collect();
                    let kind = match fault {
                        NumberFault::NoDigits => format!("a number with no digits after {}", &number[..2]),
                        NumberFault::Scale => "a decimal with more than 19 digits after the point".to_string(),
                        NumberFault::Octal => "an octal number".to_string(),
                        NumberFault::Suffix(length) => format!("a number with the suffix {}", &number[number.len() - length..]),
                        NumberFault::TooBig => "a number above 18446744073709551615".to_string(),
                    };
                    Tok::Unknown(names.id(&kind), line)
                }
                // An invisible character is named by its code point, decision 0125. A bot cannot see it in quotes.
                LexKind::BadChar => match word.chars().next() {
                    // ponytail: the four Hangul fillers are letters that print as nothing. Upgrade: a table of the default-ignorable code points.
                    Some(ch) if !(ch.is_ascii_graphic() || ch.is_alphanumeric()) || matches!(ch, '\u{115F}' | '\u{1160}' | '\u{3164}' | '\u{FFA0}') => Tok::Unknown(names.id(&format!("U+{:04X} in a contract", ch as u32)), line),
                    _ => Tok::Unknown(names.id(&format!("'{word}' in a contract")), line),
                },
            }
        })
        .collect()
}

/// The fold of a contract line, decisions 0106, 0109 and 0124. The core does it, from the tables of the shell by id. A name that is not in the table of
/// words cannot be in the tokens, so it is left out. An enumerator that is not in the table still takes its place among the members of its enum.
fn fold_names(toks: Vec<Tok>, names: &Names) -> Vec<Tok> {
    // `Flag::Write` of a valued enum is the integer token of its value, decision 0175.
    // ponytail: a quantifier or a parameter that spells the name of the enum does not hide it, and two valued enums of one plain name take the first. Upgrade: the core folds it.
    let mut valued = Vec::new();
    let mut at = 0;
    while at < toks.len() {
        if let (Tok::Ident(a), Some(Tok::ColonColon), Some(Tok::Ident(b))) = (toks[at], toks.get(at + 1), toks.get(at + 2)) {
            let value = names.valued.iter().find(|(n, _)| n == names.text(a)).and_then(|(_, vs)| vs.iter().find(|(m, _)| m == names.text(*b)));
            if let Some((_, v)) = value {
                valued.push(Tok::Int(*v));
                at += 3;
                continue;
            }
        }
        valued.push(toks[at]);
        at += 1;
    }
    let toks = valued;
    let mut missing = u32::MAX;
    let mut folds = cplusp_core::fold::Folds { constants: Vec::new(), reals: Vec::new(), shadow: Vec::new(), enums: Vec::new(), enumerators: Vec::new() };
    folds.constants = names.constants.iter().filter_map(|(c, v)| Some((names.find(c)?, *v))).collect();
    folds.reals = names.reals.iter().filter_map(|(c, negative, m, q)| Some((names.find(c)?, *negative, *m, *q))).collect();
    folds.shadow = names.shadow.iter().filter_map(|n| names.find(n)).collect();
    for (plain, key, list) in &names.enums {
        folds.enums.extend(names.find(plain).map(|id| (id, *key)));
        for member in list {
            folds.enumerators.push((*key, names.find(member).unwrap_or_else(|| {
                missing -= 1;
                missing
            })));
        }
    }
    let folded = cplusp_core::fold::fold(&toks, &folds);
    // A static data member is one name, `Registry::last_id`, decision 0173. So is a static member function, `Tally::valid`, decision 0174. The lexer cuts it
    // in three tokens. The longest chain that names a global or a static member function is one name.
    // ponytail: a quantifier `forall Registry :: last_id == 0` over a bound name that spells a qualifier of a global is read as that global. Upgrade: the core merges.
    let mut out = Vec::new();
    let mut i = 0;
    while i < folded.len() {
        if let Tok::Ident(first) = folded[i] {
            let mut text = names.text(first).to_string();
            let mut best = None;
            let mut j = i;
            while let (Some(Tok::ColonColon), Some(Tok::Ident(next))) = (folded.get(j + 1), folded.get(j + 2)) {
                text = format!("{text}::{}", names.text(*next));
                j += 2;
                if names.globals.contains(&text) || names.statics.contains(&text) {
                    best = Some((j, text.clone()));
                }
            }
            if let Some((end, id)) = best.and_then(|(end, text)| Some((end, names.find(&text)?))) {
                out.push(Tok::Ident(id));
                i = end + 1;
                continue;
            }
        }
        // A bare call in the contract of a static member function names a static of its class, decision 0174. A functor of that name stays.
        if let (Tok::Ident(bare), Some(Tok::LParen), Some(class)) = (folded[i], folded.get(i + 1), &names.class) {
            let word = names.text(bare);
            let after_scope = i > 0 && matches!(folded[i - 1], Tok::ColonColon | Tok::Arrow);
            let qualified = format!("{class}::{word}");
            if !after_scope && !names.functors.iter().any(|f| f == word) && names.statics.contains(&qualified) {
                if let Some(id) = names.find(&qualified) {
                    out.push(Tok::Ident(id));
                    i += 1;
                    continue;
                }
            }
        }
        out.push(folded[i]);
        i += 1;
    }
    out
}

/// The names of the parameters of a declaration, in order. A parameter with no name is `'N` by its place, as in `function`.
fn param_names(v: Vec<String>, names: &mut Names) -> CNames {
    let ids: Vec<u32> = v.into_iter().enumerate().map(|(i, n)| names.id(&if n.is_empty() { format!("'{i}") } else { n })).collect();
    ids.into_iter().rev().fold(CNames::Nil, |rest, n| CNames::Cons(n, Box::new(rest)))
}

/// The contract word that a line reads when C++ finds a name of that spelling from the function, or none, decision 0158. The plugin lists such a word
/// as hidden, and the hidden names are in `shadow`. A parameter of the declaration that the line is above is in `params`, though the definition may name it
/// otherwise. A name of C++ with no line that reads the word is no clash.
fn word_clash(toks: &[Tok], params: &[String], names: &Names) -> Option<&'static str> {
    toks.iter()
        .filter_map(|t| match t {
            Tok::Eps => Some("eps"),
            Tok::Eta => Some("eta"),
            Tok::DblMax => Some("DBL_MAX"),
            _ => None,
        })
        .find(|w| params.iter().chain(&names.shadow).any(|n| n == w))
}

fn word_clash_sentence(word: &str) -> String {
    format!("{word} in the contract is a contract word, and a C++ name too. Rename the C++ name.")
}

/// The contract lines as the core's list. A word other than the four of the grammar has no rule, so its text is not parsed.
/// The core refuses the line by its word, and refuses a word in the wrong place. A line that the parser refuses, or that ends in a backslash, is `Bad`, and the core refuses it
/// with that refusal.
fn conds(v: Vec<JCond>, names: &mut Names) -> Conds {
    let mut items = Vec::new();
    for c in v {
        let line = names.place(&c.file, c.line);
        names.contracts.insert(line, (c.kind.clone(), c.text.trim().to_string()));
        // A backslash at the end splices the next line into the comment. The line the author wrote is not the one the plugin read.
        let entries: Vec<(CondKind, Expr)> = if c.text.ends_with('\\') || c.kind.ends_with('\\') {
            vec![(CondKind::Bad(Refusal::Backslash(line)), Expr::Int(0))]
        } else if c.kind == "modifies" || c.kind == "reads" {
            // `//@ reads a, b` is the same, one line for each global, decision 0173.
            // `//@ modifies a, b` is one line for each name, decision 0108. A name may have parts, `Tally::count_`, and the core refuses it as no reference
            // parameter, decision 0110. A line of any other form is one that names no name, and the core refuses it as a form it cannot read.
            let word = |w: &str| w.starts_with(|ch: char| ch.is_ascii_alphabetic() || ch == '_') && w.chars().all(|ch| ch.is_ascii_alphanumeric() || ch == '_');
            let listed: Vec<&str> = c.text.split(',').map(str::trim).collect();
            let kind = if c.kind == "reads" { CondKind::Reads } else { CondKind::Modifies };
            if listed.iter().all(|n| n.split("::").all(word)) {
                listed.into_iter().map(|n| (kind, Expr::Name(names.id(n)))).collect()
            } else {
                vec![(kind, Expr::Int(0))]
            }
        } else {
            vec![match c.kind.as_str() {
                "requires" | "ensures" | "invariant" | "decreases" => {
                    let want = match c.kind.as_str() {
                        "requires" => CondKind::Requires,
                        "ensures" => CondKind::Ensures,
                        "invariant" => CondKind::Invariant,
                        _ => CondKind::Decreases,
                    };
                    let toks = lex(&c.text, line, names);
                    // A contract word that a name of C++ also spells is refused, decision 0158.
                    let clash = word_clash(&toks, &c.params, names);
                    let toks = fold_names(toks, names);
                    if let Some(word) = clash {
                        names.said.insert(line, word_clash_sentence(word));
                        (CondKind::Bad(Refusal::Syntax(line)), Expr::Int(0))
                    // A call to an undeclared name is refused by `sentence` at this line, so the core refuses the line as a form it cannot read.
                    } else if names.bad_calls.contains_key(&line) {
                        (CondKind::Bad(Refusal::Syntax(line)), Expr::Int(0))
                    } else {
                        match parse_contract(&toks, line) {
                            Ok(e) => (want, e),
                            Err(r) => (CondKind::Bad(r), Expr::Int(0)),
                        }
                    }
                }
                // The index of a range-for, decision 0143: one name. Any other form is one the translator cannot read.
                "index" => {
                    let name = c.text.trim();
                    if name.starts_with(|ch: char| ch.is_ascii_alphabetic() || ch == '_') && readable(name) {
                        // The shell folds a constant and an enumerator before the core sees them, so a name of one is not new, decision 0144.
                        let taken = names.constants.iter().any(|(k, _)| k == name) || names.enums.iter().any(|e| e.2.iter().any(|m| m == name));
                        if taken {
                            (CondKind::Bad(Refusal::IndexName(names.id(name), line)), Expr::Int(0))
                        } else {
                            (CondKind::Index, Expr::Name(names.id(name)))
                        }
                    } else {
                        (CondKind::Bad(Refusal::Syntax(line)), Expr::Int(0))
                    }
                }
                word => (CondKind::Other(names.id(word)), Expr::Int(0)),
            }]
        };
        for (kind, e) in entries {
            items.push((kind, e, line, param_names(c.params.clone(), names)));
        }
    }
    items.into_iter().rev().fold(Conds::Nil, |rest, (k, e, l, p)| Conds::Cons((k, e, l, p), Box::new(rest)))
}

// ------------------------------------------------------------------ the companion file

/// The sentence for a word of a companion file that is not allowed.
fn only_functions(word: &str) -> String {
    format!("{word}: a companion file can hold only functions, predicates and lemmas.")
}

/// A declaration of the companion file: its name, the line of the name, and whether it is a lemma.
type Declared = (String, u32, bool);

/// The refusals of a companion file as (line, sentence), and the declarations it holds, decisions 0080 and 0123. The core reads the bytes, and the
/// shell writes the sentences, puts them in order and removes the copies. A file with a refusal declares no name.
fn scan_companion(text: &str) -> (Vec<(u32, String)>, Vec<Declared>) {
    // ponytail: the core reads a file under 4 GiB, so a longer one is refused at line 1. Upgrade: none planned.
    if text.len() >= u32::MAX as usize {
        return (vec![(1, "a companion file this long cannot be read.".to_string())], Vec::new());
    }
    let bytes = text.as_bytes().to_vec();
    let scan = cplusp_core::companion::scan_companion(&bytes);
    let word = |start: usize, end: usize| text[start..end].to_string();
    let mut refused: Vec<(u32, String)> = scan
        .refusals
        .into_iter()
        .map(|(line, why)| {
            let said = match why {
                CompanionRefusal::Char => "a character that a companion file cannot hold.".to_string(),
                CompanionRefusal::Word(start, end) => only_functions(&word(start, end)),
                CompanionRefusal::Quote => only_functions("\""),
                CompanionRefusal::At => only_functions("@"),
                CompanionRefusal::Attribute => only_functions("{:"),
                CompanionRefusal::ModelName(start, end) => format!("{}: a name that the model uses.", word(start, end)),
                CompanionRefusal::Unclosed => "a comment that does not end.".to_string(),
            };
            (line, said)
        })
        .collect();
    refused.sort();
    refused.dedup();
    let declared = scan.declared.into_iter().map(|(start, end, line, lemma)| (word(start, end), line, lemma)).collect();
    (refused, declared)
}

// ------------------------------------------------------------------ names that Dafny can read

/// Every name in an expression that the Dafny text will print.
fn expr_names<'a>(e: &'a JExpr, out: &mut Vec<&'a str>) {
    match e {
        JExpr::Var(v, _) | JExpr::Move(v, _) | JExpr::Step(v, ..) => out.push(v),
        JExpr::Bin(_, a, b) | JExpr::Divide(_, a, b, _) | JExpr::Shr(a, b, _) | JExpr::Bits(_, a, b, _) | JExpr::Index(a, b) | JExpr::Subspan(a, b) | JExpr::Fill(a, b) => {
            expr_names(a, out);
            expr_names(b, out);
        }
        JExpr::CountIf(v, x, _, t) => {
            out.push(x);
            expr_names(v, out);
            expr_names(t, out);
        }
        JExpr::Cond(c, a, b) => {
            expr_names(c, out);
            expr_names(a, out);
            expr_names(b, out);
        }
        JExpr::Not(a) | JExpr::Neg(a) | JExpr::Cast(_, a) | JExpr::Paren(a) | JExpr::Brace(a) | JExpr::Size(a) | JExpr::Back(a) | JExpr::Empty(a) | JExpr::Copy(a, ..) | JExpr::Field(a, _) | JExpr::HasValue(a) | JExpr::Value(a) | JExpr::Holds(_, a) | JExpr::GetAlt(_, a) | JExpr::Wrap(a) => expr_names(a, out),
        JExpr::Call(_, _, args, _) | JExpr::Construct(_, args) | JExpr::List(args) => args.iter().for_each(|a| expr_names(a, out)),
        JExpr::Lit(..) | JExpr::Bool(_) | JExpr::RealLit(..) | JExpr::Ratio(..) | JExpr::Nullopt | JExpr::EmptyVec | JExpr::Enumerator(..) | JExpr::Unknown(..) => {}
    }
}

/// Every contract text of a statement: the assert and apply lines and the lines of the loops, at any depth, for decision 0176.
fn stmt_conds<'a>(s: &'a JStmt, out: &mut Vec<&'a str>) {
    match s {
        JStmt::Assert(c) | JStmt::Apply(c) => out.push(&c.text),
        JStmt::If(_, t, f, _) => t.iter().chain(f).for_each(|s| stmt_conds(s, out)),
        JStmt::Block(body, _) => body.iter().for_each(|s| stmt_conds(s, out)),
        JStmt::Switch(_, _, cases, _) => cases.iter().flat_map(|(_, body)| body).for_each(|s| stmt_conds(s, out)),
        JStmt::While(_, cs, body, _) | JStmt::RangeFor(_, _, _, cs, body, _) => {
            out.extend(cs.iter().map(|c| c.text.as_str()));
            body.iter().for_each(|s| stmt_conds(s, out));
        }
        JStmt::For(init, _, step, cs, body, _) => {
            out.extend(cs.iter().map(|c| c.text.as_str()));
            stmt_conds(init, out);
            stmt_conds(step, out);
            body.iter().for_each(|s| stmt_conds(s, out));
        }
        _ => {}
    }
}

/// Whether a contract text calls the name: the name, not part of a longer name, then `(`.
fn calls_name(text: &str, name: &str) -> bool {
    text.match_indices(name).any(|(i, _)| !text[..i].ends_with(|c: char| c.is_ascii_alphanumeric() || c == '_') && text[i + name.len()..].trim_start().starts_with('('))
}

fn stmt_names<'a>(s: &'a JStmt, out: &mut Vec<&'a str>) {
    match s {
        JStmt::Return(e, _) => expr_names(e, out),
        JStmt::If(c, t, f, _) => {
            expr_names(c, out);
            t.iter().chain(f).for_each(|s| stmt_names(s, out));
        }
        JStmt::Local(n, _, e, _) | JStmt::Assign(n, e, _) => {
            out.push(n);
            expr_names(e, out);
        }
        JStmt::Step(n, ..) => out.push(n),
        JStmt::SetField(_, e, _) | JStmt::SetThroughField(_, _, e, _) => expr_names(e, out),
        JStmt::Sort(v, _) | JStmt::PopField(v, _) => out.push(v),
        JStmt::SortBy(v, a, b, _, e, _) => {
            out.extend([v, a, b].map(String::as_str));
            expr_names(e, out);
        }
        JStmt::PushBack(v, e, _) | JStmt::PushField(v, e, _) => {
            out.push(v);
            expr_names(e, out);
        }
        JStmt::SetIndex(v, i, e, _) | JStmt::SetFieldAt(v, i, e, _) => {
            out.push(v);
            expr_names(i, out);
            expr_names(e, out);
        }
        JStmt::Switch(e, _, cases, _) => {
            expr_names(e, out);
            cases.iter().flat_map(|(_, body)| body).for_each(|s| stmt_names(s, out));
        }
        JStmt::SetRefField(p, _, e, _) | JStmt::SetOwnField(p, _, e, _) => {
            out.push(p);
            expr_names(e, out);
        }
        JStmt::Call(_, _, args, _) => args.iter().for_each(|a| expr_names(a, out)),
        JStmt::Exit(_) | JStmt::Assert(_) | JStmt::Apply(_) => {}
        JStmt::Block(body, _) => body.iter().for_each(|s| stmt_names(s, out)),
        JStmt::While(c, _, body, _) => {
            expr_names(c, out);
            body.iter().for_each(|s| stmt_names(s, out));
        }
        JStmt::For(init, c, step, _, body, _) => {
            stmt_names(init, out);
            expr_names(c, out);
            stmt_names(step, out);
            body.iter().for_each(|s| stmt_names(s, out));
        }
        JStmt::RangeFor(x, _, seq, _, body, _) => {
            out.push(x);
            expr_names(seq, out);
            body.iter().for_each(|s| stmt_names(s, out));
        }
        JStmt::Unknown(..) => {}
    }
}

/// The first name of the function with a character that Dafny cannot read. A parameter with no name is `'N` and Dafny reads it.
// ponytail: the function is refused, and its callers are refused at the call. Upgrade: a mangling that escapes such characters.
fn unreadable_name(f: &JFunction) -> Option<&str> {
    // A signature the core refuses has no method, so the Dafny text prints none of its names. The core's refusal stands.
    if matches!(f.ret, JTy::Other(_)) || f.params.iter().any(|(_, t)| matches!(t, JTy::Other(_))) {
        return None;
    }
    let mut names = vec![if operator_word(&f.name).is_some() { "op" } else { dafny_word(&f.name) }];
    names.extend(f.params.iter().map(|(n, _)| n.as_str()));
    f.body.iter().for_each(|s| stmt_names(s, &mut names));
    // A static data member or a static member function has `::` in its name, and the mangling makes it `'`, decisions 0173 and 0174.
    // The fresh local of a constructor with a body is `'init'` and its field, decision 0179. C++ cannot write `'`, so it clashes with no name.
    // The fresh local of a chain on a temporary is `'chain'` and a number, decision 0183.
    names.into_iter().find(|n| !readable(&n.strip_prefix("'init'").or_else(|| n.strip_prefix("'chain'")).unwrap_or(n).replace("::", "_")))
}

/// `operator()` is a name of C++ that the Dafny text prints as `call`, decision 0098. Every other name stays as it is.
/// The readable name of a free operator function, decision 0175: `operator+` is `op'plus`. C++ cannot write `'`, so it clashes with no name.
fn operator_word(name: &str) -> Option<&'static str> {
    Some(match name {
        "operator+" => "op'plus",
        "operator-" => "op'minus",
        "operator*" => "op'times",
        "operator/" => "op'div",
        "operator%" => "op'mod",
        "operator&" => "op'bitand",
        "operator|" => "op'bitor",
        "operator==" => "op'eq",
        "operator!=" => "op'ne",
        "operator<" => "op'lt",
        "operator<=" => "op'le",
        "operator>" => "op'gt",
        "operator>=" => "op'ge",
        _ => return None,
    })
}

fn dafny_word(name: &str) -> &str {
    if name == "operator()" {
        "call"
    } else if name == "~" {
        // The destructor is the member `~`, and its method is `c_Guard'dtor`, decision 0178.
        "dtor"
    } else {
        name
    }
}

fn readable(name: &str) -> bool {
    // The field of the base with data is `'B`, and C++ cannot write a `'`, decision 0201.
    name.strip_prefix('\'').unwrap_or(name).chars().all(|c| c.is_ascii_alphanumeric() || c == '_')
}

/// The Dafny word for a type argument: `int32` for `int32_t`, `S_Box'of'int32` for a struct, decision 0180. A type with no word is `other`.
fn type_word(t: &JTy, struct_name: &dyn Fn(&str) -> String, enum_name: &dyn Fn(&str) -> String) -> String {
    match t {
        JTy::I8 => "int8".to_string(),
        JTy::I16 => "int16".to_string(),
        JTy::I32 => "int32".to_string(),
        JTy::I64 => "int64".to_string(),
        JTy::U8 => "uint8".to_string(),
        JTy::U16 => "uint16".to_string(),
        JTy::U32 => "uint32".to_string(),
        JTy::U64 => "uint64".to_string(),
        JTy::F64 => "real".to_string(),
        JTy::Struct(k) => format!("S_{}", struct_name(k)),
        JTy::Enum(k) => format!("E_{}", enum_name(k)),
        JTy::Bool => "bool".to_string(),
        _ => "other".to_string(),
    }
}

/// Whether a type argument has a word in the model, decision 0180. ponytail: a scalar, a struct or an enum. Upgrade: a word for a sequence, an optional.
fn has_word(t: &JTy) -> bool {
    matches!(t, JTy::I8 | JTy::I16 | JTy::I32 | JTy::I64 | JTy::U8 | JTy::U16 | JTy::U32 | JTy::U64 | JTy::Bool | JTy::F64 | JTy::Struct(_) | JTy::Enum(_))
}

/// Whether an instance of a class template has a type argument with no Dafny name, decision 0188.
fn unnamed_arguments(st: &JStruct) -> bool {
    st.of.iter().any(|t| !has_word(t))
}

/// Sets `full` of each struct: its name, then for an instance of a class template `'of'` and the word of each argument joined by `'`, decision 0188.
fn set_full_names(items: &mut [(Item, &str)]) {
    let enums: Vec<(String, String)> = items
        .iter()
        .filter_map(|(i, _)| match i {
            Item::Enum(en) => Some((en.key.clone(), en.name.clone())),
            _ => None,
        })
        .collect();
    // An argument is a struct that comes earlier or later in the lines, so each name is built from the arguments, which are smaller types.
    fn full(st: &JStruct, items: &[(Item, &str)], enums: &[(String, String)]) -> String {
        if st.of.is_empty() {
            return st.name.clone();
        }
        let struct_name = |k: &str| items.iter().find_map(|(i, _)| match i { Item::Struct(g) if g.key == k => Some(full(g, items, enums)), _ => None }).unwrap_or_default();
        let enum_name = |k: &str| enums.iter().find(|(key, _)| key == k).map(|(_, n)| n.clone()).unwrap_or_default();
        format!("{}'of'{}", st.name, st.of.iter().map(|t| type_word(t, &struct_name, &enum_name)).collect::<Vec<_>>().join("'"))
    }
    let fulls: Vec<(String, String)> = items.iter().filter_map(|(i, _)| match i { Item::Struct(st) => Some((st.key.clone(), full(st, items, &enums))), _ => None }).collect();
    for (item, _) in items.iter_mut() {
        if let Item::Struct(st) = item {
            st.full = fulls.iter().find(|(k, _)| *k == st.key).map(|(_, f)| f.clone()).unwrap_or_default();
        }
    }
}

/// The first name of the struct, its own or a field's, with a character that Dafny cannot read.
fn unreadable_struct_name(st: &JStruct) -> Option<&str> {
    std::iter::once(st.name.as_str()).chain(st.fields.iter().map(|(n, _)| n.as_str())).find(|n| !readable(n))
}

/// The first name of the enum, its own or an enumerator's, with a character that Dafny cannot read, decision 0109.
fn unreadable_enum_name(en: &JEnum) -> Option<&str> {
    std::iter::once(en.name.as_str()).chain(en.enumerators.iter().map(String::as_str)).find(|n| !readable(n))
}

fn function(f: JFunction, names: &mut Names) -> Function {
    let name = names.id(&f.key);
    names.file = f.file;
    names.class = f.class;
    names.shadow = f.params.iter().map(|(n, _)| n.clone()).chain(f.hidden.iter().cloned()).collect();
    let mut used = Vec::new();
    f.body.iter().for_each(|s| stmt_names(s, &mut used));
    names.shadow.extend(used.into_iter().map(str::to_string));
    // The names that a contract may call as a functor, decision 0098.
    names.functors = f.params.iter().filter(|(_, t)| matches!(t, JTy::Struct(_))).map(|(n, _)| n.clone()).collect();
    if let (Some((_, JTy::This(k) | JTy::ThisMut(k) | JTy::Iface(k) | JTy::IfaceMut(k))), _) | (_, JTy::This(k)) = (f.params.first(), &f.ret) {
        names.functors.extend(names.struct_fields.get(k).cloned().unwrap_or_default());
    }
    // A constructor reads the members of the value it builds, decision 0094.
    names.this_members = match (f.params.first(), &f.ret) {
        (Some((_, JTy::This(k) | JTy::ThisMut(k) | JTy::Iface(k) | JTy::IfaceMut(k))), _) | (_, JTy::This(k)) => names.members.get(k).cloned().unwrap_or_default(),
        _ => Vec::new(),
    };
    // A parameter with no name is named by its position, as `'N`. C++ cannot write that, so it clashes with no name. The mangling makes it `v_'N`.
    let ps: Vec<(u32, Ty)> = f
        .params
        .into_iter()
        .enumerate()
        .map(|(i, (n, t))| (names.id(&if n.is_empty() { format!("'{i}") } else { n }), ty(t, names)))
        .collect();
    let params = ps.into_iter().rev().fold(Params::Nil, |rest, (n, t)| Params::Cons((n, t), Box::new(rest)));
    let ret = ty(f.ret, names);
    let line = names.here(f.line);
    Function { name, line, params, ret, trusted: f.trusted.is_some() || f.interface, conds: conds(f.conds, names), body: stmts(f.body, names) }
}

// ------------------------------------------------------------------ the Dafny text

pub const PRELUDE: &str = r"newtype int8 = x: int | -0x80 <= x < 0x80
newtype int16 = x: int | -0x8000 <= x < 0x8000
newtype uint16 = x: int | 0 <= x < 0x1_0000
newtype int32 = x: int | -0x8000_0000 <= x < 0x8000_0000
newtype int64 = x: int | -0x8000_0000_0000_0000 <= x < 0x8000_0000_0000_0000
newtype uint8 = x: int | 0 <= x < 0x100
newtype uint32 = x: int | 0 <= x < 0x1_0000_0000
newtype uint64 = x: int | 0 <= x < 0x1_0000_0000_0000_0000
datatype Option<T> = None | Some(value: T)
datatype Variant<A, B> = Alt0(alt0: A) | Alt1(alt1: B)
type Vec<T> = s: seq<T> | |s| < 0x1_0000_0000_0000_0000 witness []
function trunc_size(x: int): nat { if x < 0 then -x else x }
lemma MulNonneg(a: int, b: int)
  requires 0 <= a && 0 <= b
  ensures 0 <= a * b
{
  if a > 0 {
    MulNonneg(a - 1, b);
    assert a * b == (a - 1) * b + b;
  }
}
lemma MulBound(a: int, b: int, c: int, d: int)
  requires 0 <= a <= c && 0 <= b <= d
  ensures 0 <= a * b <= c * d
{
  MulNonneg(a, b);
  MulNonneg(c - a, b);
  MulNonneg(c, d - b);
  assert (c - a) * b == c * b - a * b;
  assert c * (d - b) == c * d - c * b;
}
lemma trunc_div_size(x: nat, m: nat)
  requires m >= 1
  ensures x / m <= x
{
  if m > 1 {
    assert x / m * m <= x;
  }
}
function trunc_div(a: int, b: int): int
  requires b != 0
  ensures trunc_size(trunc_div(a, b)) <= trunc_size(a)
  ensures trunc_div(a, b) < 0 ==> (a < 0) != (b < 0)
{
  trunc_div_size(trunc_size(a), trunc_size(b));
  var q := trunc_size(a) / trunc_size(b);
  if (a < 0) == (b < 0) then q else -q
}
function trunc_rem(a: int, b: int): int
  requires b != 0
  ensures trunc_size(trunc_rem(a, b)) < trunc_size(b)
  ensures trunc_rem(a, b) < 0 ==> a < 0
{
  var r := trunc_size(a) % trunc_size(b);
  if a < 0 then -r else r
}
function CountIf<T>(s: seq<T>, p: T -> bool): nat
  ensures CountIf(s, p) <= |s|
{
  if |s| == 0 then 0 else CountIf(s[..|s| - 1], p) + (if p(s[|s| - 1]) then 1 else 0)
}
function Back<T>(s: seq<T>): T
  requires |s| > 0
{
  s[|s| - 1]
}
function PopBack<T>(s: seq<T>): seq<T>
  requires |s| > 0
{
  s[..|s| - 1]
}
";

/// The model of std::sort, decision 0161: the file of the divergence tests as it is. The shell keeps no copy.
pub const ALGORITHM: &str = include_str!("../../../divergence/dafny/Algorithm.dfy");

/// The model of a double operation, decision 0154: the file of the divergence tests as it is. The shell keeps no copy.
pub const DOUBLE: &str = include_str!("../../../divergence/dafny/Double.dfy");

/// The model of `a >> n`, decision 0106. It follows the methods when one of them shifts, so a file with no shift has no `decreases` line of its own.
pub const SHR: &str = r"function shr(a: int, n: int, w: int): int
  requires 0 <= n < w
  ensures a >= 0 ==> 0 <= shr(a, n, w) <= a
  ensures a < 0 ==> a <= shr(a, n, w) < 0
  decreases n
{
  if n == 0 then a else shr(a, n - 1, w) / 2
}
";

/// The model of `&` and `|` on unsigned integers, decision 0175: two recursive functions on the bits and the lemmas that prove their laws. It follows the
/// methods when one of them has a bit operator, and each such method calls `Laws()` first.
pub const BITS: &str = r#"function Pow2(k: nat): nat { if k == 0 then 1 else 2 * Pow2(k - 1) }
function BitAnd(a: nat, b: nat): nat decreases a { if a == 0 || b == 0 then 0 else (if a % 2 == 1 && b % 2 == 1 then 1 else 0) + 2 * BitAnd(a / 2, b / 2) }
function BitOr(a: nat, b: nat): nat decreases a + b { if a == 0 then b else if b == 0 then a else (if a % 2 == 1 || b % 2 == 1 then 1 else 0) + 2 * BitOr(a / 2, b / 2) }
lemma AndLe(a: nat, b: nat) ensures BitAnd(a, b) <= a && BitAnd(a, b) <= b { if a != 0 && b != 0 { AndLe(a / 2, b / 2); } }
lemma OrBound(a: nat, b: nat, k: nat) requires a < Pow2(k) && b < Pow2(k) ensures BitOr(a, b) < Pow2(k)
{ if a != 0 && b != 0 { OrBound(a / 2, b / 2, k - 1); } }
lemma Absorb(a: nat, b: nat) ensures BitAnd(BitOr(a, b), a) == a
{ if a != 0 && b != 0 { Absorb(a / 2, b / 2); } else if a != 0 { AndSelf(a); } }
lemma AndSelf(a: nat) ensures BitAnd(a, a) == a { if a != 0 { AndSelf(a / 2); } }
lemma AndComm(a: nat, b: nat) ensures BitAnd(a, b) == BitAnd(b, a) { if a != 0 && b != 0 { AndComm(a / 2, b / 2); } }
lemma AndAbsorb(a: nat, b: nat) ensures BitAnd(a, BitAnd(a, b)) == BitAnd(a, b) && BitAnd(b, BitAnd(a, b)) == BitAnd(a, b)
{ if a != 0 && b != 0 { AndAbsorb(a / 2, b / 2); } }
lemma SubsetOr(c: nat, d: nat, a: nat) requires BitAnd(c, a) == a ensures BitAnd(BitOr(c, d), a) == a
{ if c != 0 && d != 0 && a != 0 { SubsetOr(c / 2, d / 2, a / 2); } else if c == 0 { } else if d == 0 { } else { AndLe(c, a); } }
lemma SubsetAnd(a: nat, b: nat, w: nat) ensures (BitAnd(BitAnd(a, b), w) == w) <==> (BitAnd(a, w) == w && BitAnd(b, w) == w)
{ if a != 0 && b != 0 && w != 0 { SubsetAnd(a / 2, b / 2, w / 2); } else { AndLe(a, b); AndLe(a, w); AndLe(b, w); AndLe(BitAnd(a, b), w); } }
lemma Laws()
  ensures forall a: nat, b: nat {:trigger BitAnd(a, b)} :: BitAnd(a, b) <= a && BitAnd(a, b) <= b
  ensures forall a: nat, b: nat {:trigger BitOr(a, b)} :: a < 0x1_0000_0000 && b < 0x1_0000_0000 ==> BitOr(a, b) < 0x1_0000_0000
  ensures forall a: nat, b: nat {:trigger BitAnd(BitOr(a, b), a)} :: BitAnd(BitOr(a, b), a) == a
  ensures forall a: nat, b: nat {:trigger BitAnd(BitOr(a, b), b)} :: BitAnd(BitOr(a, b), b) == b
  ensures forall a: nat, b: nat {:trigger BitAnd(a, BitAnd(a, b))} :: BitAnd(a, BitAnd(a, b)) == BitAnd(a, b)
  ensures forall a: nat, b: nat {:trigger BitAnd(b, BitAnd(a, b))} :: BitAnd(b, BitAnd(a, b)) == BitAnd(a, b)
  ensures forall c: nat, d: nat, a: nat {:trigger BitAnd(BitOr(c, d), a)} :: BitAnd(c, a) == a ==> BitAnd(BitOr(c, d), a) == a
  ensures forall a: nat, b: nat, w: nat {:trigger BitAnd(BitAnd(a, b), w)} :: (BitAnd(BitAnd(a, b), w) == w) <==> (BitAnd(a, w) == w && BitAnd(b, w) == w)
{
  forall a: nat, b: nat ensures BitAnd(a, b) <= a && BitAnd(a, b) <= b { AndLe(a, b); }
  forall a: nat, b: nat | a < 0x1_0000_0000 && b < 0x1_0000_0000 ensures BitOr(a, b) < 0x1_0000_0000 { Pow2_32(); OrBound(a, b, 32); }
  forall a: nat, b: nat ensures BitAnd(BitOr(a, b), a) == a { Absorb(a, b); }
  forall a: nat, b: nat ensures BitAnd(BitOr(a, b), b) == b { OrComm(a, b); Absorb(b, a); }
  forall a: nat, b: nat ensures BitAnd(a, BitAnd(a, b)) == BitAnd(a, b) { AndAbsorb(a, b); }
  forall a: nat, b: nat ensures BitAnd(b, BitAnd(a, b)) == BitAnd(a, b) { AndAbsorb(a, b); }
  forall c: nat, d: nat, a: nat | BitAnd(c, a) == a ensures BitAnd(BitOr(c, d), a) == a { SubsetOr(c, d, a); }
  forall a: nat, b: nat, w: nat ensures (BitAnd(BitAnd(a, b), w) == w) <==> (BitAnd(a, w) == w && BitAnd(b, w) == w) { SubsetAnd(a, b, w); }
}
lemma Pow2_32() ensures Pow2(32) == 0x1_0000_0000 { assert {:fuel Pow2, 34} Pow2(32) == 0x1_0000_0000; }
lemma OrComm(a: nat, b: nat) ensures BitOr(a, b) == BitOr(b, a) { if a != 0 && b != 0 { OrComm(a / 2, b / 2); } }
"#;

fn dscalar(s: Scalar, names: &Names) -> String {
    match s {
        Scalar::I32 => "int32".to_string(),
        Scalar::I64 => "int64".to_string(),
        Scalar::U8 => "uint8".to_string(),
        Scalar::U32 => "uint32".to_string(),
        Scalar::U64 => "uint64".to_string(),
        Scalar::Bool => "bool".to_string(),
        Scalar::Struct(k) => names.datatypes[&k].clone(),
        Scalar::Own(k) => format!("Option<{}>", names.datatypes[&k]),
    }
}

fn dty(t: DTy, names: &Names) -> String {
    match t {
        DTy::Int32 => "int32".to_string(),
        DTy::Int64 => "int64".to_string(),
        DTy::UInt8 => "uint8".to_string(),
        DTy::UInt32 => "uint32".to_string(),
        DTy::UInt64 => "uint64".to_string(),
        DTy::Int8 => "int8".to_string(),
        DTy::Int16 => "int16".to_string(),
        DTy::UInt16 => "uint16".to_string(),
        DTy::Bool => "bool".to_string(),
        DTy::Real => "real".to_string(),
        DTy::Seq(s) => format!("Vec<{}>", dscalar(s, names)),
        DTy::Arr(s, k) => format!("Arr'{k}<{}>", dscalar(s, names)),
        DTy::Struct(k) | DTy::Enum(k) | DTy::Iface(k) => names.datatypes[&k].clone(),
        DTy::Opt(s) => format!("Option<{}>", dscalar(s, names)),
        DTy::Variant(a, b) => format!("Variant<{}, {}>", dscalar(a, names), dscalar(b, names)),
        // A method that gives no value has no `result`, so no caller prints this type.
        DTy::Void => String::new(),
    }
}

/// The type of a local. A local sequence is a plain `seq`, because `push_back` may grow it past the bound of `Vec`, decision 0160.
fn local_ty(t: DTy, names: &Names) -> String {
    match t {
        DTy::Seq(s) | DTy::Arr(s, _) => format!("seq<{}>", dscalar(s, names)),
        _ => dty(t, names),
    }
}

/// Whether a result type is a `std::unique_ptr` of the interface `base`, decision 0199. The plugin writes it as `Struct`. An interface by value is refused.
fn holds_interface(t: DTy, base: u32) -> bool {
    matches!(t, DTy::Opt(Scalar::Struct(k)) if k == base)
}

/// The name of a member in C++. A virtual function whose name two share has the name, `'` and its parameter types in the table, decision 0210.
fn plain_member(n: &str) -> &str {
    n.split('\'').next().unwrap_or(n)
}

/// The Dafny name of the upcast from the class `d` to its interface `b`, `f_D'B`, decision 0166. The names of the model are the names of the datatypes, without
/// `S_`, so two classes of one plain name stay apart.
fn upcast_name(d: u32, b: u32, names: &Names) -> String {
    let short = |k: u32| names.datatypes[&k].strip_prefix("S_").unwrap_or(&names.datatypes[&k]).to_string();
    format!("f_{}'{}", short(d), short(b))
}

fn dop(o: BinOp) -> &'static str {
    match o {
        BinOp::Add => "+",
        BinOp::Sub => "-",
        BinOp::Mul => "*",
        BinOp::Div => "/",
        BinOp::Rem => "%",
        BinOp::Lt => "<",
        BinOp::Le => "<=",
        BinOp::Gt => ">",
        BinOp::Ge => ">=",
        BinOp::Eq => "==",
        BinOp::Ne => "!=",
        BinOp::And => "&&",
        BinOp::Or => "||",
        BinOp::Implies => "==>",
        // A bit operator prints as a call of the prelude, in `dexpr`, decision 0175.
        BinOp::BitAnd => "BitAnd",
        BinOp::BitOr => "BitOr",
    }
}

/// The one mangling of a C++ variable for Dafny, for code and contract alike. The prefix `v_` keeps a name clear of the words Dafny
/// reserves, such as `old` and `function`, and of `result`. The contract word `result` is no name: it is `Tok::Result`, and prints as
/// `result`. A method has the prefix `c_`, so a variable never hides a method, decision 0060.
// An unnamed parameter is `v_'N` and an overload is `c_{plain}'{k}`. C++ cannot write `'` in a name, so no clash is possible.
fn mangle(name: &str) -> String {
    // A static data member `Registry::last_id` is `v_Registry'last_id`, decision 0173.
    format!("v_{}", name.replace("::", "'"))
}

fn dargs(args: &DArgs, names: &Names) -> Vec<String> {
    let mut shown = Vec::new();
    let mut rest = args;
    while let List::Cons(a, next) = rest {
        shown.push(dexpr(a, names));
        rest = next;
    }
    shown
}

/// Every operator has its parentheses, so Dafny's precedence never matters.
fn dexpr(e: &DExpr, names: &Names) -> String {
    match e {
        DExpr::Lit(n) => n.to_string(),
        DExpr::Bool(b) => b.to_string(),
        DExpr::Var(v) => mangle(names.text(*v)),
        DExpr::Result => "result".to_string(),
        DExpr::Bin(o, a, b) => format!("({} {} {})", dexpr(a, names), dop(*o), dexpr(b, names)),
        DExpr::Not(a) => format!("(!{})", dexpr(a, names)),
        DExpr::Neg(a) => format!("(-{})", dexpr(a, names)),
        DExpr::AsInt(a) => format!("({} as int)", dexpr(a, names)),
        DExpr::Conv(t, a) => format!("({} as {})", dexpr(a, names), dty(*t, names)),
        DExpr::Field(a, f) => format!("{}.f_{}", dexpr(a, names), names.text(*f)),
        DExpr::IsSome(a) => format!("{}.Some?", dexpr(a, names)),
        DExpr::Get(a) => format!("{}.value", dexpr(a, names)),
        DExpr::Is(second, a) => format!("{}.Alt{}?", dexpr(a, names), u8::from(*second)),
        DExpr::Alt(second, a) => format!("{}.alt{}", dexpr(a, names), u8::from(*second)),
        DExpr::Nothing => "None".to_string(),
        DExpr::EmptySeq => "[]".to_string(),
        DExpr::Just(a) => format!("Some({})", dexpr(a, names)),
        DExpr::Enumerator(k, i) => format!("{}'{}", names.datatypes[k], names.enums.iter().find(|e| e.1 == *k).and_then(|e| e.2.get(*i as usize)).map_or("'unknown", String::as_str)),
        DExpr::Ctor(k, args) => format!("{}({})", names.datatypes[k], dargs(args, names).join(", ")),
        DExpr::BitOp(o, a, b) => format!("{}({}, {})", dop(*o), dexpr(a, names), dexpr(b, names)),
        DExpr::SeqLit(args) => format!("[{}]", dargs(args, names).join(", ")),
        DExpr::SeqFill(n, x) => format!("seq({} as int, _ => {})", dexpr(n, names), dexpr(x, names)),
        DExpr::Len(a) => format!("|{}|", dexpr(a, names)),
        DExpr::Back(a) => format!("Back({})", dexpr(a, names)),
        DExpr::PopBack(a) => format!("PopBack({})", dexpr(a, names)),
        DExpr::Index(a, i) => format!("{}[{}]", dexpr(a, names), dexpr(i, names)),
        DExpr::Append(a, e) => format!("({} + [{}])", dexpr(a, names), dexpr(e, names)),
        DExpr::CountIf(s, x, t, e) => format!("CountIf({}, ({}: {}) => {})", dexpr(s, names), mangle(names.text(*x)), dty(*t, names), dexpr(e, names)),
        // The exact decimal: the digits `d`, with `k` of them after the point and at least one.
        DExpr::RealLit(d, k) => {
            let digits = format!("{:0>width$}", d, width = *k as usize + 1);
            let (whole, fraction) = digits.split_at(digits.len() - *k as usize);
            format!("{whole}.{}", if fraction.is_empty() { "0" } else { fraction })
        }
        DExpr::FOp(o, a, b) => {
            names.rounds.set(true);
            names.double.set(true);
            let f = match o {
                BinOp::Add => "fadd",
                BinOp::Sub => "fsub",
                BinOp::Mul => "fmul",
                _ => "fdiv",
            };
            format!("{f}({}, {})", dexpr(a, names), dexpr(b, names))
        }
        DExpr::FromInt(a) => {
            names.exact.set(true);
            names.double.set(true);
            format!("fint({} as int)", dexpr(a, names))
        }
        DExpr::IntAbs(a) => format!("trunc_size({})", dexpr(a, names)),
        DExpr::Abs(a) => {
            names.double.set(true);
            format!("abs({})", dexpr(a, names))
        }
        DExpr::Eps => {
            names.double.set(true);
            "EPS".to_string()
        }
        DExpr::Eta => {
            names.double.set(true);
            "ETA".to_string()
        }
        DExpr::DblMax => {
            names.double.set(true);
            "MAX".to_string()
        }
        // The value of a final class as its interface, decision 0166.
        DExpr::Upcast(d, b, a) => format!("{}({})", upcast_name(*d, *b, names), dexpr(a, names)),
        // The value after a call of a lemma, decision 0167. A lemma is called before the value in the body of a function.
        DExpr::Lemma(l, args, e) => format!("{}({}); {}", names.text(*l), dargs(args, names).join(", "), dexpr(e, names)),
        // A local of a pure body, decision 0172. It stands at the head of a function body, so it needs no parentheses.
        DExpr::Let(x, t, v, b) => format!("var {}: {} := {}; {}", mangle(names.text(*x)), local_ty(*t, names), dexpr(v, names), dexpr(b, names)),
        DExpr::SetAt(a, i, e) => format!("{}[{} := {}]", dexpr(a, names), dexpr(i, names), dexpr(e, names)),
        DExpr::Drop(a, k) => format!("{}[{}..]", dexpr(a, names), dexpr(k, names)),
        DExpr::Take(a, j) => format!("{}[..{}]", dexpr(a, names), dexpr(j, names)),
        DExpr::Slice(a, i, j) => format!("{}[{}..{}]", dexpr(a, names), dexpr(i, names), dexpr(j, names)),
        // The prefix `b_` keeps a bound name apart from `v_` and `c_` names.
        DExpr::Forall(j, b) => format!("(forall b_{}: int :: {})", names.text(*j), dexpr(b, names)),
        DExpr::Exists(j, b) => format!("(exists b_{}: int :: {})", names.text(*j), dexpr(b, names)),
        DExpr::Bound(j) => format!("b_{}", names.text(*j)),
        DExpr::Apply(f, args) => format!("{}({})", names.text(*f), dargs(args, names).join(", ")),
        DExpr::After => "v_this'".to_string(),
        DExpr::Out(x) => format!("{}'", mangle(names.text(*x))),
        DExpr::FCall(k, args) => format!("{}({})", names.functions[k], dargs(args, names).join(", ")),
        DExpr::TDiv(a, b) => format!("trunc_div({}, {})", dexpr(a, names), dexpr(b, names)),
        DExpr::TRem(a, b) => format!("trunc_rem({}, {})", dexpr(a, names), dexpr(b, names)),
        DExpr::DivIn(a, b, t) => format!("(trunc_div({}, {}) as {})", dexpr(a, names), dexpr(b, names), dty(*t, names)),
        // The let checks that the quotient fits T before it gives the remainder, as C++ requires. `q'` cannot clash with a C++ name.
        DExpr::RemIn(a, b, t) => {
            let (a, b, t) = (dexpr(a, names), dexpr(b, names), dty(*t, names));
            format!("(var q' := (trunc_div({a}, {b}) as {t}); (trunc_rem({a}, {b}) as {t}))")
        }
        DExpr::ShrIn(a, n, t, w) => format!("(shr({}, {}, {w}) as {})", dexpr(a, names), dexpr(n, names), dty(*t, names)),
        DExpr::Ite(c, a, b) => format!("(if {} then {} else {})", dexpr(c, names), dexpr(a, names), dexpr(b, names)),
        DExpr::Chain(o1, o2, a, b, c) => format!("({} {} {} {} {})", dexpr(a, names), dop(*o1), dexpr(b, names), dop(*o2), dexpr(c, names)),
        // The prefix `v_'t` keeps a temporary apart from C++ names, companion names and the dropped values `v_'r`.
        // A read outside a `Pre` prints a name that Dafny cannot resolve, so it fails loudly and never reads an older temporary.
        DExpr::Temp(t) => names.temp_base.get().map_or("v_'unbound".to_string(), |base| format!("v_'t{}", base + t)),
    }
}

/// The Dafny name of each function by the id of its key, with the method prefix `c_`. `c_{plain}` when the plain name is unique among the file's functions, else
/// `c_{plain}'{k}`, with k counting the functions of that plain name in file order from 1.
type Methods = HashMap<u32, String>;

/// What the prover's report needs of one line of the Dafny text, decision 0068: the place of the C++ line it comes from, and the places
/// of the contract lines in scope there. Those are the requires lines before it and the invariants of the loops around it. On an
/// invariant or a decreases line, `own` holds all the invariants of that loop. They are assumed when the loop keeps an invariant, not when it starts.
pub struct Line {
    pub place: u32,
    pub scope: Vec<u32>,
    pub own: Vec<u32>,
}

/// The map from the lines of the Dafny text to C++, decision 0068. `lines[n - 1]` is line n of the text. A blank line has none.
pub struct Map {
    pub lines: Vec<Option<Line>>,
    /// The indexes in `lines` of the companion file's text, decision 0079.
    pub companion: std::ops::Range<usize>,
    /// The declarations of the companion file as (line in the Dafny text, is a lemma), in order, decision 0099.
    pub decls: Vec<(usize, bool)>,
    /// The file and line of each place.
    pub places: Vec<(String, u32)>,
    /// The word and text of the contract line at a place, as the author wrote them.
    pub contracts: HashMap<u32, (String, String)>,
    /// The check of each override, decision 0165.
    pub lemmas: Vec<LemmaMap>,
    /// The lines of the Dafny text that copy lines of an interface, decision 0166.
    pub copies: Vec<(std::ops::Range<usize>, Vec<std::ops::Range<usize>>)>,
}

/// The lines of the lemma that checks one override, for the report of prove, decision 0165. `lines` are line numbers of the Dafny text, `place` is the
/// place of the override, `own` are the lines of its requires, which the lemma claims, and `requires` are the places of the requires lines of the interface.
pub struct LemmaMap {
    pub lines: std::ops::Range<usize>,
    pub place: u32,
    pub own: Vec<usize>,
    pub requires: Vec<u32>,
    /// The lines of its requires clauses, which copy the requires lines of the interface.
    pub requires_lines: Vec<usize>,
    /// The lines of the lemma calls of its body, and the lines of the method of the override, decision 0167.
    pub body: std::ops::Range<usize>,
    pub method: std::ops::Range<usize>,
    /// The places of the requires lines of the override.
    pub own_places: Vec<u32>,
    /// `B::f`, for the sentences.
    pub of: String,
}

pub struct Translation {
    pub dafny: String,
    /// The number of methods in the Dafny text, with a body or without, decision 0080.
    pub methods: usize,
    /// Each trusted function that has a method, in the order of the file: its file, the line of its name, its name and its reason, decision 0102.
    pub trusted: Vec<(String, u32, String, String)>,
    pub refusals: Vec<Refusing>,
    /// The model calls an operation of the module `Double`, so a verdict rests on its axiom, decision 0154.
    pub rounds: bool,
    /// The model calls `fint`, so a verdict rests on the axiom `RoundExactInt`, decision 0159.
    pub exact: bool,
    /// The model calls `StdSort`, so a verdict rests on its contract, decision 0161.
    pub sorted: bool,
    /// The plain name of each interface in the model, decision 0165.
    pub interfaces: Vec<String>,
    /// The plain names of each final class and interface that a local is written through, decision 0208.
    pub downs: Vec<(String, String)>,
    pub map: Map,
}

/// The printer of the Dafny text. It writes one line at a time, and keeps the map for each line it writes.
struct Printer<'a> {
    names: &'a Names,
    /// The lines (of the Dafny text, from 1) of the functions that copy the lines of an interface: the function of a virtual function and the upcast, decision 0166.
    copies: Vec<(std::ops::Range<usize>, Vec<std::ops::Range<usize>>)>,
    /// The functions printed for the method that is being written, which copy its lines: they become copies when the method is done.
    pending: Vec<std::ops::Range<usize>>,
    /// The lines of the method of each function, by the id of its key.
    method_lines: HashMap<u32, std::ops::Range<usize>>,
    /// The lemma calls of the body of each pure member function by the id of its key, as `L(args);`, for the check of an override, decision 0167.
    calls: HashMap<u32, Vec<String>>,
    /// The type that a local unique_ptr points at, by the id of its name, as the Dafny type, for the write of decision 0169.
    owned: HashMap<u32, String>,
    /// The virtual functions that write their object, by the id of their keys. They have no function and no line in the upcast, decision 0169.
    writing: std::collections::HashSet<u32>,
    /// The const virtual functions that give no value, by the id of their keys. They write their reference parameters only, decision 0209.
    const_void: std::collections::HashSet<u32>,
    /// The names of the reference parameters of each function, by the id of its key, for the lemma that checks an override that writes.
    refs: HashMap<u32, Vec<u32>>,
    /// The pairs of a final class and its interface that a call writes a local through, by key, for the Axiom line of decision 0208.
    downs: std::collections::BTreeSet<(u32, u32)>,
    methods: &'a Methods,
    /// The result type of each method by the id of its key, for the call that drops a value, decision 0096.
    rets: &'a HashMap<u32, DTy>,
    out: String,
    lines: Vec<Option<Line>>,
    /// The contract lines in scope now.
    scope: Vec<u32>,
    /// The invariants of the loop whose invariant and decreases lines are being written.
    own: Vec<u32>,
    /// The method that is being written takes its object in and gives it back, decision 0096.
    writes: bool,
    /// The count of the names that drop a value, `v_'rN`. C++ makes `v_'N` only, and a companion file cannot start a name with `v_`.
    fresh: u32,
    /// The count of the temporaries of the method so far, `v_'tN`, decision 0104.
    temps: u32,
    /// The printer is inside a `Block`, so a `Pre` takes the base of the block, decision 0177.
    in_block: bool,
    /// The file has a bit operator, so each method with a body calls `Laws()` first, decision 0175.
    laws: bool,
}

impl Printer<'_> {
    fn put(&mut self, depth: usize, text: String, place: u32) {
        writeln!(self.out, "{}{text}", "  ".repeat(depth)).unwrap();
        self.lines.push(Some(Line { place, scope: self.scope.clone(), own: self.own.clone() }));
    }

    fn call(&self, m: u32, args: &DArgs) -> String {
        format!("{}({})", self.methods[&m], dargs(args, self.names).join(", "))
    }

    /// The Dafny names of the places that a call writes back, parted by commas, and the call `m(args)`. The arguments hold the object and
    /// the reference parameters too, decision 0108.
    /// The value of a local unique_ptr that a virtual function writes, `Owned`, comes back in a fresh local that is declared first, and the unique_ptr
    /// takes it after the call, decision 0169. The third part is those declarations, and the fourth is the writes to the unique_ptrs.
    fn update(&mut self, objs: &Objs, m: u32, args: &DArgs) -> (String, String, String, String) {
        let mut places = Vec::new();
        let (mut before, mut after) = (String::new(), String::new());
        let mut rest = objs;
        while let List::Cons(o, next) = rest {
            places.push(match o {
                Obj::Local(n) => mangle(self.names.text(*n)),
                Obj::Object => "v_this'".to_string(),
                Obj::Out(x) => format!("{}'", mangle(self.names.text(*x))),
                // The vector place of an `UpdateAt` only. It is never one of the places of the results.
                Obj::Field(_) => "v_this'".to_string(),
                Obj::Owned(v) => {
                    self.fresh += 1;
                    let temp = format!("v_'o{}", self.fresh);
                    let pointed = self.owned.get(v).cloned().unwrap_or_default();
                    before.push_str(&format!("var {temp}: {pointed}; "));
                    after.push_str(&format!(" {} := Some({temp});", mangle(self.names.text(*v))));
                    temp
                }
                // A local of a final class through a reference to its interface comes back as a value of the interface. The local takes a value of its
                // class whose upcast is that value, decision 0208. Dafny cannot find it, so the model assumes it exists: the Axiom line of `prove`.
                // ponytail: one assume for each call. Upgrade: a lemma for each pair of classes.
                Obj::Down(v, dk, bk) => {
                    self.fresh += 1;
                    let temp = format!("v_'d{}", self.fresh);
                    let (local, up) = (mangle(self.names.text(*v)), upcast_name(*dk, *bk, self.names));
                    before.push_str(&format!("var {temp}: {}; ", self.names.datatypes[bk]));
                    after.push_str(&format!(" assume {{:axiom}} exists v_'q: {} :: {up}(v_'q) == {temp}; {local} :| {up}({local}) == {temp};", self.names.datatypes[dk]));
                    self.downs.insert((*dk, *bk));
                    temp
                }
            });
            rest = next;
        }
        (places.join(", "), self.call(m, args), before, after)
    }

    /// Keep the type that a local unique_ptr points at, for the write of a virtual function, decision 0169.
    fn note(&mut self, x: u32, t: DTy) {
        match t {
            DTy::Opt(s) => {
                self.owned.insert(x, dscalar(s, self.names));
            }
            // A vector of unique_ptr keeps the type of its elements, for the write of an element, decision 0170.
            DTy::Seq(Scalar::Own(k)) => {
                self.owned.insert(x, self.names.datatypes[&k].clone());
            }
            _ => {}
        }
    }

    fn stmts(&mut self, ss: &DStmts, depth: usize) {
        let mut rest = ss;
        while let List::Cons((s, place), next) = rest {
            self.stmt(s, *place, depth);
            rest = next;
        }
    }

    /// A `while`: the condition, the invariants, the decreases lines, then the body. A `for` has its step as the last statement of the body.
    /// The `while` line and the body have the invariants of the loop in scope. The invariant and decreases lines have them as `own`.
    fn dwhile(&mut self, (c, place): (&DExpr, u32), lists: [&DConds; 2], body: &DStmts, step: Option<(&DStmt, u32)>, depth: usize) {
        let mut invariants = Vec::new();
        let mut cs = lists[0];
        while let List::Cons((_, line), next) = cs {
            invariants.push(*line);
            cs = next;
        }
        // The `while` line is the condition and the end of the loop. Dafny checks it under all the invariants.
        let outer = self.scope.len();
        self.scope.extend(invariants.iter().copied());
        self.put(depth, format!("while {}", dexpr(c, self.names)), place);
        self.scope.truncate(outer);
        self.own = invariants.clone();
        for (word, list) in ["invariant", "decreases"].into_iter().zip(lists) {
            let mut cs = list;
            while let List::Cons((e, line), next) = cs {
                self.put(depth + 1, format!("{word} {}", dexpr(e, self.names)), *line);
                cs = next;
            }
        }
        self.own.clear();
        self.put(depth, "{".to_string(), place);
        let kept = self.scope.len();
        self.scope.extend(invariants);
        self.stmts(body, depth + 1);
        if let Some((step, at)) = step {
            self.stmt(step, at, depth + 1);
        }
        self.scope.truncate(kept);
        self.put(depth, "}".to_string(), place);
    }

    fn stmt(&mut self, s: &DStmt, place: u32, depth: usize) {
        let names = self.names;
        match s {
            // Dafny's `return e;` would need both out-parameters of a method that writes its object.
            DStmt::Return(e) if self.writes => {
                self.put(depth, format!("result := {};", dexpr(e, names)), place);
                self.put(depth, "return;".to_string(), place);
            }
            DStmt::Return(e) => self.put(depth, format!("return {};", dexpr(e, names)), place),
            DStmt::SetField(f, e) => self.put(depth, format!("v_this' := v_this'.(f_{} := {});", names.text(*f), dexpr(e, names)), place),
            DStmt::SetOut(x, e) => self.put(depth, format!("{}' := {};", mangle(names.text(*x)), dexpr(e, names)), place),
            DStmt::SetOutField(x, f, e) => {
                let x = format!("{}'", mangle(names.text(*x)));
                self.put(depth, format!("{x} := {x}.(f_{} := {});", names.text(*f), dexpr(e, names)), place);
            }
            // Decision 0186: the pointer owns a value, and the write keeps the other fields.
            DStmt::SetOwnField(n, f, e) => {
                let n = mangle(names.text(*n));
                self.put(depth, format!("{n} := Some({n}.value.(f_{} := {}));", names.text(*f), dexpr(e, names)), place);
            }
            // Decision 0197: the field holds a pointer, and the write keeps the other fields of what it owns.
            DStmt::SetThroughField(f, g, e) => {
                let f = names.text(*f);
                self.put(depth, format!("v_this' := v_this'.(f_{f} := Some(v_this'.f_{f}.value.(f_{} := {})));", names.text(*g), dexpr(e, names)), place);
            }
            DStmt::Update(objs, m, args) => {
                let (object, call, before, after) = self.update(objs, *m, args);
                match self.rets.get(m) {
                    Some(DTy::Void) | None => self.put(depth, format!("{before}{object} := {call};{after}"), place),
                    // The value is dropped into a fresh local.
                    Some(t) => {
                        self.fresh += 1;
                        let r = format!("v_'r{}", self.fresh);
                        self.put(depth, format!("{before}var {r}: {}; {r}, {object} := {call};{after}", dty(*t, names)), place);
                    }
                }
            }
            DStmt::UpdateAt(vec, index, objs, m, args) => {
                // The element comes back in a fresh local, and the vector takes it at the index, decision 0170. The index is read twice, and the core checked that
                // the call does not change it.
                let (places, call, before, after) = self.update(objs, *m, args);
                let temp = format!("v_'e{}", self.fresh);
                self.fresh += 1;
                let (name, written) = match vec {
                    Obj::Local(v) => (*v, mangle(names.text(*v))),
                    Obj::Out(v) | Obj::Owned(v) => (*v, format!("{}'", mangle(names.text(*v)))),
                    Obj::Object => (0, "v_this'".to_string()),
                    // The core never takes a class through its interface as the vector of an element write, decisions 0208 and 0217.
                    Obj::Down(..) => unreachable!("decision 0217: the core makes Down only for an argument"),
                    // The element of a vector field of the new object, decision 0204. The field keeps the type of its elements in `owned`.
                    Obj::Field(f) => (*f, format!("v_this'.f_{}", names.text(*f))),
                };
                let pointed = self.owned.get(&name).cloned().unwrap_or_default();
                let mut gives = vec![temp.clone()];
                if !places.is_empty() {
                    gives.push(places);
                }
                let result = match self.rets.get(m) {
                    Some(DTy::Void) | None => String::new(),
                    Some(t) => {
                        self.fresh += 1;
                        let r = format!("v_'r{}", self.fresh);
                        gives.insert(0, r.clone());
                        format!("var {r}: {}; ", dty(*t, names))
                    }
                };
                let element = format!("{written}[{} := Some({temp})]", dexpr(index, names));
                let update = match vec {
                    Obj::Field(f) => format!("v_this'.(f_{} := {element})", names.text(*f)),
                    _ => element,
                };
                self.put(
                    depth,
                    format!("{before}{result}var {temp}: {pointed}; {} := {call}; {} := {update};{after}", gives.join(", "), if matches!(vec, Obj::Field(_)) { "v_this'" } else { &written }),
                    place,
                );
            }
            DStmt::LocalUpdate(x, t, objs, m, args) => {
                self.note(*x, *t);
                let (object, call, before, after) = self.update(objs, *m, args);
                let x = mangle(names.text(*x));
                self.put(depth, format!("{before}var {x}: {}; {x}, {object} := {call};{after}", dty(*t, names)), place);
            }
            DStmt::Match(d, k, cases) => {
                self.put(depth, format!("match {} {{", dexpr(d, names)), place);
                let mut rest = &**cases;
                while let List::Cons((i, body), next) = rest {
                    let case = dexpr(&DExpr::Enumerator(*k, *i), names);
                    self.put(depth + 1, format!("case {case} => {{"), place);
                    self.stmts(body, depth + 2);
                    self.put(depth + 1, "}".to_string(), place);
                    rest = next;
                }
                self.put(depth, "}".to_string(), place);
            }
            DStmt::CallStmt(m, args) => {
                let call = self.call(*m, args);
                self.put(depth, format!("{call};"), place);
            }
            DStmt::Exit => self.put(depth, "return;".to_string(), place),
            // The calls run in order on the line of the statement. Each sets a temporary that the later calls and the statement read.
            // ponytail: each call is placed on the line of its statement. Upgrade: carry the line of each call in `DCalls::Cons`.
            DStmt::Pre(calls, inner) => {
                // Inside a `Block` the temporaries of the whole block share one base, decision 0177.
                let base = if self.in_block { names.temp_base.get().unwrap_or(self.temps) } else { self.temps };
                let outer = names.temp_base.replace(Some(base));
                let mut rest = calls;
                while let List::Cons(pre, next) = rest {
                    match pre {
                        DPre::Call(t, ty, m, args) => {
                            let call = self.call(*m, args);
                            self.put(depth, format!("var v_'t{}: {} := {call};", base + t, dty(*ty, names)), place);
                            self.temps = self.temps.max(base + t + 1);
                        }
                        // A call that writes back: its value goes to the temporary and the places take the rest, decision 0177.
                        DPre::Update(t, ty, objs, m, args) => {
                            let (places, call, before, after) = self.update(objs, *m, args);
                            let temp = format!("v_'t{}", base + t);
                            let gives = if places.is_empty() { temp.clone() } else { format!("{temp}, {places}") };
                            self.put(depth, format!("{before}var {temp}: {}; {gives} := {call};{after}", dty(*ty, names)), place);
                            self.temps = self.temps.max(base + t + 1);
                        }
                        // `x++` and `++x` inside an expression, decision 0177. The write has the check of an assignment: the sum is converted back.
                        DPre::Step(t, ty, x, up, prefix, out) => {
                            let x = if *out { format!("{}'", mangle(names.text(*x))) } else { mangle(names.text(*x)) };
                            let (temp, ty) = (format!("v_'t{}", base + t), dty(*ty, names));
                            let write = format!("{x} := (({x} as int) {} 1) as {ty};", if *up { "+" } else { "-" });
                            if *prefix {
                                self.put(depth, write, place);
                                self.put(depth, format!("var {temp}: {ty} := {x};"), place);
                            } else {
                                self.put(depth, format!("var {temp}: {ty} := {x};"), place);
                                self.put(depth, write, place);
                            }
                            self.temps = self.temps.max(base + t + 1);
                        }
                    }
                    rest = next;
                }
                self.stmt(inner, place, depth);
                names.temp_base.set(outer);
            }
            // The statements of one lowered `return`, each on the line of the `return`. Their temporaries share one base, decision 0177.
            DStmt::Block(ss) => {
                let base = if self.in_block { names.temp_base.get().unwrap_or(self.temps) } else { self.temps };
                let outer = names.temp_base.replace(Some(base));
                let was = std::mem::replace(&mut self.in_block, true);
                self.stmts(ss, depth);
                self.in_block = was;
                names.temp_base.set(outer);
            }
            // A bare block of the source is a block of the model, decision 0178.
            DStmt::Scope(ss) => {
                self.put(depth, "{".to_string(), place);
                self.stmts(ss, depth + 1);
                self.put(depth, "}".to_string(), place);
            }
            // The destructors of the locals that die, in order. Each keeps its own place.
            DStmt::Dtors(ss) => self.stmts(ss, depth),
            DStmt::SetResult(e) => self.put(depth, format!("result := {};", dexpr(e, names)), place),
            DStmt::DeclTemp(t, ty) => {
                let base = names.temp_base.get().unwrap_or(self.temps);
                self.put(depth, format!("var v_'t{}: {};", base + t, dty(*ty, names)), place);
                self.temps = self.temps.max(base + t + 1);
            }
            DStmt::AssignTemp(t, e) => {
                let base = names.temp_base.get().unwrap_or(self.temps);
                self.put(depth, format!("v_'t{} := {};", base + t, dexpr(e, names)), place);
            }
            DStmt::Assert(e) => self.put(depth, format!("assert {};", dexpr(e, names)), place),
            // The statement, then each name that it moved is null, decision 0171.
            DStmt::Moved(inner, moved) => {
                self.stmt(inner, place, depth);
                let mut rest = moved;
                while let List::Cons(x, next) = rest {
                    self.put(depth, format!("{} := None;", mangle(names.text(*x))), place);
                    rest = next;
                }
            }
            // The statement, then the vector that it moved has any value, decision 0185.
            DStmt::Gone(inner, w, out) => {
                self.stmt(inner, place, depth);
                let w = if *out { format!("{}'", mangle(names.text(*w))) } else { mangle(names.text(*w)) };
                self.put(depth, format!("{w} :| true;"), place);
            }
            DStmt::Apply(l, args) => self.put(depth, format!("{}({});", names.text(*l), dargs(args, names).join(", ")), place),
            // `std::sort` of a whole vector with the default `<`, decision 0161. `StdSort` is the method of the module `Algorithm`.
            DStmt::Sort(target, t) => {
                names.sorted.set(true);
                let (target, t) = (dexpr(target, names), dty(*t, names));
                self.put(depth, format!("{target} := StdSort({target}, (a: {t}, b: {t}) => a < b);"), place)
            }
            // A local vector is a plain `seq`, because `push_back` may grow it past the bound of `Vec`, as for a vector given back, decision 0160.
            DStmt::SortBy(target, a, b, t, body) => {
                names.sorted.set(true);
                let (target, t) = (dexpr(target, names), dty(*t, names));
                let (a, b) = (mangle(names.text(*a)), mangle(names.text(*b)));
                self.put(depth, format!("{target} := StdSort({target}, ({a}: {t}, {b}: {t}) => {});", dexpr(body, names)), place)
            }
            DStmt::Local(x, t, e) => {
                self.note(*x, *t);
                self.put(depth, format!("var {}: {} := {};", mangle(names.text(*x)), local_ty(*t, names), dexpr(e, names)), place)
            }
            DStmt::LocalCall(x, t, m, args) => {
                self.note(*x, *t);
                let call = self.call(*m, args);
                self.put(depth, format!("var {}: {} := {call};", mangle(names.text(*x)), local_ty(*t, names)), place);
            }
            DStmt::ReturnCall(m, args) => {
                let call = self.call(*m, args);
                self.put(depth, format!("result := {call};"), place);
                self.put(depth, "return;".to_string(), place);
            }
            // `return f(a);` of a call that writes back: the value goes to `result`, then the places, decisions 0108 and 0174.
            DStmt::ReturnUpdate(objs, m, args) => {
                let (object, call, before, after) = self.update(objs, *m, args);
                self.put(depth, format!("{before}result, {object} := {call};{after}"), place);
                self.put(depth, "return;".to_string(), place);
            }
            DStmt::Assign(x, e) => self.put(depth, format!("{} := {};", mangle(names.text(*x)), dexpr(e, names)), place),
            DStmt::AssignCall(x, m, args) => {
                let call = self.call(*m, args);
                self.put(depth, format!("{} := {call};", mangle(names.text(*x))), place);
            }
            DStmt::While(c, inv, dec, body) => self.dwhile((c, place), [inv, dec], body, None, depth),
            DStmt::For(init, init_place, c, inv, dec, body, step, step_place) => {
                self.stmt(init, *init_place, depth);
                self.dwhile((c, place), [inv, dec], body, Some((step, *step_place)), depth);
            }
            DStmt::If(c, t, f) => {
                self.put(depth, format!("if {} {{", dexpr(c, names)), place);
                self.stmts(t, depth + 1);
                if matches!(**f, List::Nil) {
                    self.put(depth, "}".to_string(), place);
                } else {
                    self.put(depth, "} else {".to_string(), place);
                    self.stmts(f, depth + 1);
                    self.put(depth, "}".to_string(), place);
                }
            }
        }
    }

    /// The method header line, with no contract and no body.
    /// A method that gives no value has no `result`. One that writes its object also gives it back as `this'`, of the type of its first
    /// parameter, decision 0096.
    fn header(&mut self, name: u32, params: &DParams, ret: DTy, (writes, axiom): (bool, bool), outs: &[(u32, DTy)], place: u32) {
        let mut shown = Vec::new();
        let mut ps = params;
        while let List::Cons((n, t), next) = ps {
            shown.push(format!("{}: {}", mangle(self.names.text(*n)), dty(*t, self.names)));
            ps = next;
        }
        let mut gives = Vec::new();
        if ret != DTy::Void {
            gives.push(format!("result: {}", dty(ret, self.names)));
        }
        if let (true, List::Cons((_, t), _)) = (writes, params) {
            gives.push(format!("v_this': {}", dty(*t, self.names)));
        }
        // The reference parameters that the method gives back follow, in the order of the parameters, decision 0108.
        // A vector by reference is a plain `seq` when it is given back: `push_back` may grow it past the bound of `Vec`, as C++ may grow it past
        // `max_size()`, and a failed `push_back` never returns, decision 0148.
        gives.extend(outs.iter().map(|(n, t)| match t {
            DTy::Seq(s) => format!("{}': seq<{}>", mangle(self.names.text(*n)), dscalar(*s, self.names)),
            _ => format!("{}': {}", mangle(self.names.text(*n)), dty(*t, self.names)),
        }));
        let returns = if gives.is_empty() { String::new() } else { format!(" returns ({})", gives.join(", ")) };
        self.out.push('\n');
        self.lines.push(None);
        let attribute = if axiom { "{:axiom} " } else { "" };
        self.put(0, format!("method {attribute}{}({}){returns}", self.methods[&name], shown.join(", ")), place);
    }

    /// The Dafny function of a pure member function, right before its method, decision 0090. Its requires lines are those of the method.
    fn function(&mut self, m: &Method, body: &DExpr, place: u32) {
        let mut shown = Vec::new();
        let mut ps = &m.params;
        while let List::Cons((n, t), next) = ps {
            shown.push(format!("{}: {}", mangle(self.names.text(*n)), dty(*t, self.names)));
            ps = next;
        }
        // The lemmas that the body calls, for the check of an override, decision 0167.
        let mut calls = Vec::new();
        // A local before a lemma call is repeated, so the arguments of the call resolve. A local after the last call is not.
        let mut cur = body;
        let mut used = 0;
        loop {
            match cur {
                DExpr::Lemma(l, args, rest) => {
                    calls.push(format!("{}({});", self.names.text(*l), dargs(args, self.names).join(", ")));
                    used = calls.len();
                    cur = rest;
                }
                DExpr::Let(x, t, v, rest) => {
                    calls.push(format!("var {}: {} := {};", mangle(self.names.text(*x)), local_ty(*t, self.names), dexpr(v, self.names)));
                    cur = rest;
                }
                _ => break,
            }
        }
        calls.truncate(used);
        if !calls.is_empty() {
            self.calls.insert(m.name, calls);
        }
        self.out.push('\n');
        self.lines.push(None);
        let start = self.lines.len() + 1;
        self.put(0, format!("function {}({}): (result: {})", self.names.functions[&m.name], shown.join(", "), dty(m.ret, self.names)), place);
        let mut cs = &m.requires;
        while let List::Cons((e, line), next) = cs {
            self.put(1, format!("requires {}", dexpr(e, self.names)), *line);
            self.scope.push(*line);
            cs = next;
        }
        // The ensures lines of the member function, which Dafny proves on the body, decision 0213.
        let mut cs = &m.fensures;
        while let List::Cons((e, line), next) = cs {
            self.put(1, format!("ensures {}", dexpr(e, self.names)), *line);
            cs = next;
        }
        self.put(0, "{".to_string(), place);
        // A function of a file with a bit operator calls `Laws()` first, as a method does, so the value of a bit operator fits its type, decision 0176.
        self.put(1, format!("{}{}", if self.laws { "Laws(); " } else { "" }, dexpr(body, self.names)), place);
        self.put(0, "}".to_string(), place);
        self.scope.clear();
        // The function of a pure member has the requires lines and the body of its method, so a failure in it stands for the failure of the method, decision 0167.
        self.pending.push(start..self.lines.len() + 1);
    }

    /// The lemma that checks one override against the contract of its interface, decision 0165. Dafny proves that the requires lines of the override follow from
    /// those of the interface, and that the function of the override keeps the ensures lines of the interface. The lemma has no body.
    fn lemma(&mut self, up: &DUpcast, o: &DOverride, place: u32, of: String) -> LemmaMap {
        let names = self.names;
        let (this, f) = (format!("v_this: {}", names.datatypes[&up.derived]), &names.functions[&o.derived]);
        let mut ps = vec![this];
        let mut args = vec!["v_this".to_string()];
        let mut rest = &o.params;
        while let List::Cons((n, t), next) = rest {
            ps.push(format!("{}: {}", mangle(names.text(*n)), dty(*t, names)));
            args.push(mangle(names.text(*n)));
            rest = next;
        }
        // An override that writes has no function. Its lemma takes the object after the call, the reference parameters after it, and the result, and Dafny
        // proves that the promise of the override gives each ensures line of the interface, decision 0169.
        let writes = self.writing.contains(&o.base);
        if writes {
            if !self.const_void.contains(&o.base) {
                ps.push(format!("v_this': {}", names.datatypes[&up.derived]));
            }
            let mut rest = &o.params;
            while let List::Cons((n, t), next) = rest {
                if self.refs[&o.derived].contains(n) {
                    ps.push(format!("{}': {}", mangle(names.text(*n)), dty(*t, names)));
                }
                rest = next;
            }
            if o.ret != DTy::Void {
                ps.push(format!("result: {}", dty(o.ret, names)));
            }
        }
        self.out.push('\n');
        self.lines.push(None);
        let start = self.lines.len() + 1;
        self.put(0, format!("lemma {f}check'{}({})", names.class_names[&up.base], ps.join(", ")), place);
        let mut requires = Vec::new();
        let mut requires_lines = Vec::new();
        let mut cs = &o.requires;
        while let List::Cons((e, line), next) = cs {
            requires_lines.push(self.lines.len() + 1);
            self.put(1, format!("requires {}", dexpr(e, names)), *line);
            requires.push(*line);
            cs = next;
        }
        let mut own = Vec::new();
        let mut cs = &o.own;
        while let List::Cons((e, line), next) = cs {
            own.push(self.lines.len() + 1);
            self.put(1, format!("ensures {}", dexpr(e, names)), *line);
            cs = next;
        }
        let promise: Vec<String> = {
            let mut all = Vec::new();
            let mut cs = &o.promise;
            while let List::Cons((e, _), next) = cs {
                all.push(dexpr(e, names));
                cs = next;
            }
            all
        };
        let mut cs = &o.ensures;
        while let List::Cons((e, line), next) = cs {
            if !writes {
                self.put(1, format!("ensures var result: {} := {f}({}); {}", dty(o.ret, names), args.join(", "), dexpr(e, names)), *line);
            } else if promise.is_empty() {
                self.put(1, format!("ensures {}", dexpr(e, names)), *line);
            } else {
                self.put(1, format!("ensures ({}) ==> {}", promise.join(") && ("), dexpr(e, names)), *line);
            }
            cs = next;
        }
        // The body calls the lemmas that the override calls, with the names that the lemma shares with its function, decision 0167.
        let mut body = self.lines.len() + 1..self.lines.len() + 1;
        match self.calls.get(&o.derived).cloned() {
            Some(calls) => {
                self.put(0, "{".to_string(), place);
                let first = self.lines.len() + 1;
                for call in calls {
                    self.put(1, call, place);
                }
                body = first..self.lines.len() + 1;
                self.put(0, "}".to_string(), place);
            }
            None => self.put(0, "{}".to_string(), place),
        }
        let mut own_places = Vec::new();
        let mut cs = &o.own;
        while let List::Cons((_, line), next) = cs {
            own_places.push(*line);
            cs = next;
        }
        LemmaMap { lines: start..self.lines.len() + 1, place, own, requires, requires_lines, body, method: self.method_lines.get(&o.derived).cloned().unwrap_or(0..0), own_places, of }
    }

    fn axiom_function(&mut self, m: &Method, place: u32) {
        let names = self.names;
        let mut shown = Vec::new();
        let mut ps = &m.params;
        while let List::Cons((n, t), next) = ps {
            shown.push(format!("{}: {}", mangle(names.text(*n)), dty(*t, names)));
            ps = next;
        }
        self.out.push('\n');
        self.lines.push(None);
        let start = self.lines.len() + 1;
        self.put(0, format!("function {{:axiom}} {}({}): (result: {})", names.functions[&m.name], shown.join(", "), dty(m.ret, names)), place);
        let mut cs = &m.requires;
        while let List::Cons((e, line), next) = cs {
            self.put(1, format!("requires {}", dexpr(e, names)), *line);
            cs = next;
        }
        let mut cs = &m.ensures;
        while let List::Cons((e, line), next) = cs {
            if matches!(**next, List::Cons(..)) {
                self.put(1, format!("ensures {}", dexpr(e, names)), *line);
            }
            cs = next;
        }
        self.pending.push(start..self.lines.len() + 1);
    }

    /// The upcast from a final class to its interface, decision 0166: a function of the model with no body, which Dafny takes as given. For each virtual function
    /// of the interface, in its order, the interface function on the upcast of an object is the function of the override on the object, when the requires lines of
    /// both hold. The lemmas of the checks show that those lines are consistent. Two kinds of function have no equation: a function that writes, decision 0169,
    /// and a function whose result holds the interface, decision 0199.
    fn upcast_function(&mut self, up: &DUpcast, place: u32) {
        let names = self.names;
        let f = upcast_name(up.derived, up.base, names);
        self.out.push('\n');
        self.lines.push(None);
        let start = self.lines.len() + 1;
        self.put(0, format!("function {{:axiom}} {f}(v_this: {}): {}", names.datatypes[&up.derived], names.datatypes[&up.base]), place);
        let mut os = &up.overrides;
        while let List::Cons(o, next) = os {
            // A virtual function that writes has no function in the model, so the upcast says nothing of it, decision 0169.
            if self.writing.contains(&o.base) {
                os = next;
                continue;
            }
            // A result that holds the interface holds this upcast, so the fact would define the upcast by itself and Dafny could not show that it ends.
            // A call through the interface keeps the contract of the interface, decision 0199.
            if holds_interface(o.ret, up.base) {
                os = next;
                continue;
            }
            let mut binders = Vec::new();
            let mut args = vec![];
            let mut rest = &o.params;
            while let List::Cons((n, t), more) = rest {
                binders.push(format!("{}: {}", mangle(names.text(*n)), dty(*t, names)));
                args.push(mangle(names.text(*n)));
                rest = more;
            }
            let mut guards = Vec::new();
            for list in [&o.requires, &o.own] {
                let mut cs = list;
                while let List::Cons((e, _), more) = cs {
                    guards.push(dexpr(e, names));
                    cs = more;
                }
            }
            let tail = |this: &str| if args.is_empty() { this.to_string() } else { format!("{this}, {}", args.join(", ")) };
            let equal = format!("{}({}) == {}({})", names.functions[&o.base], tail(&format!("{f}(v_this)")), names.functions[&o.derived], tail("v_this"));
            let body = if guards.is_empty() { equal } else { format!("({}) ==> {equal}", guards.join(") && (")) };
            let line = if binders.is_empty() { body } else { format!("forall {} :: {body}", binders.join(", ")) };
            self.put(1, format!("ensures {line}"), place);
            os = next;
        }
        // It copies the lines of the methods of the interface that it names.
        let mut originals = Vec::new();
        let mut os = &up.overrides;
        while let List::Cons(o, next) = os {
            if !self.writing.contains(&o.base) && !holds_interface(o.ret, up.base) {
                originals.extend(self.method_lines.get(&o.base).cloned());
            }
            os = next;
        }
        self.copies.push((start..self.lines.len() + 1, originals));
    }

    fn method(&mut self, m: &Method, place: u32) {
        if let Some(body) = &m.function {
            self.function(m, body, place);
        }
        // A pure virtual function of an interface is also a function of the model, with its contract and no body, which Dafny takes as given, decision 0166. The
        // method says that its result is the value of the function, and that link is the last ensures line.
        if m.trusted && !m.writes && m.ret != DTy::Void && matches!(m.params, List::Cons((n, DTy::Iface(_)), _) if self.names.text(n) == "this") {
            self.axiom_function(m, place);
        }
        let outs = dparams(&m.outs);
        let mut ps = &m.params;
        while let List::Cons((n, t), next) = ps {
            self.note(*n, *t);
            ps = next;
        }
        for (n, t) in &outs {
            self.note(*n, *t);
        }
        let method_start = self.lines.len() + 1;
        self.header(m.name, &m.params, m.ret, (m.writes, m.trusted), &outs, place);
        self.temps = 0;
        // A requires line has the requires lines before it in scope, and an ensures or decreases line and the body have all of them.
        for (word, list) in [("requires", &m.requires), ("ensures", &m.ensures), ("decreases", &m.decreases)] {
            let mut cs = list;
            while let List::Cons((e, line), next) = cs {
                self.put(1, format!("{word} {}", dexpr(e, self.names)), *line);
                if word == "requires" {
                    self.scope.push(*line);
                }
                cs = next;
            }
        }
        // A trusted method has no body, and Dafny takes its contract as given, decision 0102.
        if m.trusted {
            self.scope.clear();
            self.finish_method(m.name, method_start);
            return;
        }
        self.put(0, "{".to_string(), place);
        if self.laws {
            self.put(1, "Laws();".to_string(), place);
        }
        // A method with more than one result returns a value as `result := e; return;`.
        self.writes = m.writes || !outs.is_empty();
        if m.writes {
            self.put(1, "v_this' := v_this;".to_string(), place);
        }
        for (n, _) in &outs {
            let x = mangle(self.names.text(*n));
            self.put(1, format!("{x}' := {x};"), place);
        }
        self.stmts(&m.body, 1);
        self.writes = false;
        self.put(0, "}".to_string(), place);
        self.scope.clear();
        self.finish_method(m.name, method_start);
    }

    /// The lines of a method are known. The functions printed before it copy its lines, decision 0167.
    fn finish_method(&mut self, key: u32, start: usize) {
        let range = start..self.lines.len() + 1;
        for copy in std::mem::take(&mut self.pending) {
            self.copies.push((copy, vec![range.clone()]));
        }
        self.method_lines.insert(key, range);
    }
}

/// A refusal as the place it points at and the sentence the bot reads.
fn sentence(r: Refusal, names: &Names) -> (u32, String) {
    match r {
        Refusal::Construct(k, line) => (line, format!("{}: the translator has no rule for it yet.", names.text(k))),
        Refusal::Name(n, line) => (line, format!("{} in the contract is no parameter.", names.text(n))),
        Refusal::NoField(f, line) => (line, format!("{} in the contract is no field of the struct.", names.text(f))),
        // A call through an interface that can come back, decision 0218. The name is the plain name of the class and of the function.
        Refusal::Loop(k, line) => (
            line,
            format!(
                "the call of {0} can run {0} again before it returns: the translator has no rule for it yet.",
                names.fn_classes.get(&k).map_or_else(|| names.fn_names[&k].clone(), |c| format!("{}::{}", names.class_names[c], names.fn_names[&k]))
            ),
        ),
        // A local through its interface, in a file where an interface has no final class, decision 0217.
        Refusal::Unbacked(line) => (line, "a class as a reference to its interface: the translator has no rule for it yet.".to_string()),
        Refusal::NotPure(n, line) => (line, format!("{} is no pure function. A contract calls a function with one return and no write.", names.text(n))),
        Refusal::Syntax(line) if names.shared_calls.contains(&line) => (line, format!("{} is no pure function. A contract calls a function with one return and no write.", names.bad_calls[&line].0)),
        Refusal::Syntax(line) if names.bad_calls.get(&line).is_some_and(|c| c.1 == 2) => {
            (line, format!("{} is no pure function. A contract calls a function with one return and no write.", names.bad_calls[&line].0))
        }
        Refusal::Syntax(line) if names.bad_calls.get(&line).is_some_and(|c| c.1 == 1) => (line, format!("{} is a function of the file and of the companion file. Rename one.", names.bad_calls[&line].0)),
        Refusal::Syntax(line) if names.bad_calls.contains_key(&line) => (line, format!("{} is no function of the companion file.", names.bad_calls[&line].0)),
        Refusal::Syntax(line) if names.said.contains_key(&line) => (line, names.said[&line].clone()),
        Refusal::Syntax(line) => (line, "the contract line has a form the translator cannot read.".to_string()),
        Refusal::Backslash(line) => (line, "a contract line that ends in a backslash.".to_string()),
        Refusal::Callee(n, line) => (line, format!("a call to {}, which has no model in view.", names.text(n))),
        Refusal::Place(line) => (
            line,
            "a call out of place. The translator takes a call when C++ runs it once and the statement uses its value. It takes a call that gives no value only alone.".to_string(),
        ),
        Refusal::Twice(n, line) => (line, format!("{} is declared twice in the function.", names.text(n))),
        Refusal::Convert(line) => (line, "a conversion between bool and a number.".to_string()),
        Refusal::WriteParam(n, line) => (line, format!("{} is a parameter. The translator writes only a local or a reference parameter.", names.text(n))),
        Refusal::NotRef(n, line) => (line, format!("{} on the modifies line is no reference parameter.", names.text(n))),
        // A parameter with no name has the name `'N`, so no author wrote it, decision 0155.
        Refusal::Unlisted(n, line) if names.text(n).starts_with('\'') => (line, "a reference parameter has no name. Give it a name and put it on the modifies line.".to_string()),
        Refusal::Unlisted(n, line) => (line, format!("{} is a reference parameter that the modifies line does not name.", names.text(n))),
        Refusal::NoVar(n, line) => (line, format!("{} in the {} line is no variable.", names.text(n), names.contracts.get(&line).map_or("contract", |c| c.0.as_str()))),
        Refusal::SeqParam(line) => (line, "a sequence is in the subset only as a parameter.".to_string()),
        Refusal::HoldsSeq(line) => (line, "a struct that holds a sequence has no rule yet in an optional, a pointer, a unique_ptr, or a vector that the code makes or writes.".to_string()),
        Refusal::Element(line) => (line, "an optional of a struct, a sequence of bool or a variant of one type twice has no rule yet.".to_string()),
        Refusal::Extent(line) => (line, "a sequence or an optional made from one of another type or length.".to_string()),
        Refusal::MoveRead(n, line) => (line, format!("{} moves and is read in one statement. C++ does not fix the order.", names.text(n))),
        Refusal::VecMovePlace(line) => (
            line,
            "a std::move of a std::vector has no rule here. It has a rule as the start value of a local vector and in the init list of a constructor. It also has a rule at a parameter by value of a call. That call stands alone, is the value of a return, or is the start value of a local that is no vector.".to_string(),
        ),
        Refusal::MovePlace(line) => (line, "a std::move of a std::unique_ptr has no rule here. It has a rule only in a call that stands alone, the start value of a local, a return or a field write.".to_string()),
        Refusal::NoTarget(line) => (line, "the call writes a value back, and the translator writes back only to a local or a reference parameter.".to_string()),
        Refusal::NoObject(n, line) => (line, format!("{} is a member of the struct. A requires line of a constructor has no object yet.", names.text(n))),
        Refusal::IndexName(n, line) => (line, format!("{} on the index line is a name the function already has.", names.text(n))),
        Refusal::Rounds(line) => (line, "a double operation rounds, and the translator has no rule for it yet.".to_string()),
        Refusal::Finite(n, line) if names.text(n).starts_with('\'') => (line, "a double parameter has no name. Give it a name and say std::isfinite of it in a requires line.".to_string()),
        Refusal::Finite(n, line) => (line, format!("{} is a double. A requires line needs std::isfinite({}).", names.text(n), names.text(n))),
        Refusal::FiniteResult(line) => (line, "a trusted function that gives a double needs std::isfinite(result) in an ensures line.".to_string()),
        Refusal::IndexWritten(line) => (line, "the index reads a value that the call writes: the translator has no rule for it yet.".to_string()),
        Refusal::NoMethod(d, b, n, line) => (
            line,
            format!("the override of {}::{} in {} has no method in the model, so the translator cannot check it.", names.class_names[&b], plain_member(names.text(n)), names.class_names[&d]),
        ),
        Refusal::Later(b, f, g, line) if f == g => (line, format!("the contract of {0}::{1} reads {0}::{1} itself. The translator has no rule for it yet.", names.class_names[&b], plain_member(names.text(f)))),
        Refusal::Later(b, f, g, line) => {
            let (b, f, g) = (&names.class_names[&b], plain_member(names.text(f)), plain_member(names.text(g)));
            (line, format!("the contract of {b}::{f} reads {b}::{g}, which comes later in {b}. Declare {b}::{g} first."))
        }
        Refusal::NoOverride(d, b, n, line) => (line, format!("{} has no override of {}::{}.", names.class_names[&d], names.class_names[&b], plain_member(names.text(n)))),
        Refusal::Unchecked(d, b, n, line) => (
            line,
            format!("the override of {}::{} in {} has no function in the model, so the translator cannot check it.", names.class_names[&b], plain_member(names.text(n)), names.class_names[&d]),
        ),
        // An interface with no final class over it, decision 0220.
        Refusal::NoClass(k, line) => (line, format!("{} has no final class over it in the file, so the translator cannot check its contract.", names.interface_names.get(&k).unwrap_or(&names.class_names[&k]))),
        Refusal::NotFinal(d, line) => (line, format!("{} derives from an interface and is not final. Mark it final.", names.class_names[&d])),
        Refusal::Overload(b, line) => (line, format!("{} has two virtual functions of one name. The translator has no rule for it yet.", names.class_names[&b])),
        Refusal::SortForm(line) => (line, "std::sort of another form: the translator has no rule for it yet.".to_string()),
        Refusal::VecLocal(line) => (line, "a local vector has a rule only as a copy of a vector in scope.".to_string()),
        Refusal::PassLocal(n, line) => (line, format!("{} is a local vector. A call that passes it by reference has no rule yet.", names.text(n))),
        Refusal::PassOn(n, line) => (line, format!("{} is a vector by reference. A call that passes it on has no rule yet.", names.text(n))),
        Refusal::ReadsOnly(f, g, line) => (line, format!("{} changes {}. The caller lists {} on its reads line only.", names.text(f), names.text(g), names.text(g))),
        Refusal::GlobalClash(g, line) => (line, format!("{} names a global and a parameter or a local.", names.text(g))),
        Refusal::MemberGlobal(line) => (line, "a const or virtual member function that lists a global: the translator has no rule for it yet.".to_string()),
        Refusal::GlobalType(line) => (line, "a global of this type: the translator has no rule for it yet.".to_string()),
        Refusal::SignedBits(line) => (line, "a bit operator on a signed integer: the translator has no rule for it yet.".to_string()),
        Refusal::ContractCast(line) => (line, "a static_cast in a contract that can change the value: the translator has no rule for it yet.".to_string()),
        Refusal::BraceLen(m, n, line) => (line, format!("a braced list of {m} values for a std::array of {n}: the translator has no rule for it yet.")),
        Refusal::Copy(line) => (line, "a copy of a struct with a destructor: the translator has no rule for it yet.".to_string()),
        Refusal::NoDtorContract(line) => (line, "a destructor with no contract: the translator has no rule for it yet.".to_string()),
        Refusal::TwoWrites(line) => (line, "two writes in one expression. C++ does not fix the order.".to_string()),
        Refusal::WriteRead(x, line) => (line, format!("{} has a write and a read in one expression. C++ does not fix the order.", names.text(x))),
        Refusal::LoopWrite(line) => (line, "a write in the condition of a loop: the translator has no rule for it yet.".to_string()),
        Refusal::Misplaced(line) => (
            line,
            "a contract line in the wrong place. A requires, an ensures, a modifies or a decreases line goes above a function. An invariant or a decreases line goes above a loop, and an index line above a range-for."
                .to_string(),
        ),
    }
}

/// A refusal: the file, the line and the sentence.
pub type Refusing = (String, u32, String);

/// The names and types of a list of parameters.
fn dparams(ps: &DParams) -> Vec<(u32, DTy)> {
    let mut out = Vec::new();
    let mut rest = ps;
    while let List::Cons((n, t), next) = rest {
        out.push((*n, *t));
        rest = next;
    }
    out
}

/// The Dafny file for the plugin's lines, the refusals in order each once, and the map from the lines of the file to C++. A function whose
/// signature is refused is not in the file. A function whose contract or body is refused is a method with no contract and no body. A `//@`
/// line that no function claimed is a refusal too.
pub fn translate(lines: &str, companion: Option<(&str, &str)>) -> Result<Translation> {
    // The text `operator()` is the first word, so its id is `CALL_OP`, the id that the core uses, decision 0098. The text `value` is the second, so its id is
    // `VALUE_NAME`, the member that `x.value()` calls on a struct, decision 0169. The text `reads` is the third, so its id is `READS_NAME`, decision 0173. The text `count` is the fourth, so its id is `COUNT_NAME`, decision 0175. The text `~` is the fifth, so its id is `DTOR_NAME`, decision 0178.
    let mut names = Names { words: vec!["operator()".to_string(), "value".to_string(), "reads".to_string(), "count".to_string(), "~".to_string()], ..Default::default() };
    let mut refusals = Vec::new();
    let mut funcs = Vec::new();
    let mut structs = Vec::new();
    let mut enums = Vec::new();
    // The globals of the file in the order of their definitions, decision 0173.
    let mut globals = Vec::new();
    let mut companion_ok = false;
    // The declarations of the companion file as (line of its name in the file, is a lemma), for the prover's axiom check.
    let mut decls: Vec<(usize, bool)> = Vec::new();
    if let Some((path, text)) = companion {
        let (refused, declared) = scan_companion(text);
        refusals.extend(refused.into_iter().map(|(line, sentence)| (path.to_string(), line, sentence)));
        names.declared = declared.iter().filter(|d| !d.2).map(|d| d.0.clone()).collect();
        names.lemmas = declared.iter().filter(|d| d.2).map(|d| d.0.clone()).collect();
        decls = declared.into_iter().map(|d| (d.1 as usize, d.2)).collect();
        companion_ok = refusals.is_empty();
    }
    // A function that names a struct refused for its name has no method: the Dafny text would print the name. The refusal of the struct stands.
    // A dropped function shows its other defects only after the struct is renamed.
    let mut items = Vec::new();
    for l in lines.lines().filter(|l| !l.trim().is_empty()) {
        items.push((serde_json::from_str(l).with_context(|| format!("cannot read a line of the tree: {l}"))?, l));
    }
    // The Dafny name of each struct, and of an instance of a class template with its arguments, decision 0188.
    set_full_names(&mut items);
    // A function that names a struct or an enum refused for its name has no method, with no refusal of its own.
    let mut unreadable_keys: Vec<String> = items
        .iter()
        .filter_map(|(i, _)| match i {
            Item::Struct(st) => unreadable_struct_name(st).or_else(|| unnamed_arguments(st).then_some("")).map(|_| &st.key),
            Item::Enum(en) => unreadable_enum_name(en).map(|_| &en.key),
            _ => None,
        })
        .map(|key| serde_json::to_string(key).unwrap_or_default())
        .collect();
    // A struct with a field of such a type has no datatype either, and nor has a struct that holds that struct, with no refusal of its own, decision 0115.
    let mut dropped = Vec::new();
    // The file and line of the first item that the model leaves out, decision 0130.
    let mut first_dropped: Option<(String, u32)> = None;
    loop {
        let more: Vec<(String, String)> = items
            .iter()
            .filter_map(|(i, l)| match i {
                Item::Struct(st) if unreadable_struct_name(st).is_none() && unreadable_keys.iter().any(|k| l.contains(k.as_str())) => {
                    Some((st.key.clone(), serde_json::to_string(&st.key).unwrap_or_default()))
                }
                _ => None,
            })
            .filter(|(key, _)| !dropped.contains(key))
            .collect();
        if more.is_empty() {
            break;
        }
        for (key, quoted) in more {
            dropped.push(key);
            unreadable_keys.push(quoted);
        }
    }
    for (item, l) in items {
        match item {
            Item::Orphan { orphan, file, word } => {
                let said = if word == "assert" || word == "apply" { "an assert or apply line needs a statement below it in its block." } else { "a contract line that belongs to no function." };
                refusals.push((file, orphan, said.to_string()));
            }
            Item::Global { global, ty } => {
                names.globals.push(global.clone());
                // A contract line is converted before the list of globals is, and it finds the name by its id.
                names.id(&global);
                globals.push((global, ty));
            }
            Item::Valued { valued, values } => names.valued.push((valued, values)),
            Item::Constant { constant, value } => names.constants.extend(value.parse().ok().map(|v| (constant, v))),
            Item::Real { constant, real } => names.reals.push((constant, real.0, real.1, real.2)),
            Item::Enum(en) => match unreadable_enum_name(&en) {
                Some(n) => refusals.push((en.file.clone(), en.line, format!("{n}: a name with a character Dafny cannot read."))),
                None => enums.push(en),
            },
            // An instance of a class template with a type argument that has no Dafny name, decision 0188.
            Item::Struct(st) if unnamed_arguments(&st) => {
                refusals.push((st.file.clone(), st.line, "a type argument with no Dafny name: the translator has no rule for it yet.".to_string()))
            }
            Item::Struct(st) if dropped.contains(&st.key) => {
                first_dropped.get_or_insert((st.file.clone(), st.line));
            }
            Item::Struct(st) => structs.push(st),
            Item::Function(f) if unreadable_keys.iter().any(|k| l.contains(k.as_str())) => {
                first_dropped.get_or_insert((f.file.clone(), f.line));
            }
            // A type argument with no word has no name in the model, decision 0180. ponytail: a scalar, a struct or an enum. Upgrade: a word for a sequence, an optional.
            // A signature the core refuses is reported by its own type first.
            Item::Function(f) if !matches!(f.ret, JTy::Other(_)) && !f.params.iter().any(|(_, t)| matches!(t, JTy::Other(_))) && f.of.iter().any(|t| !has_word(t)) => {
                refusals.push((f.file.clone(), f.line, "a type argument with no Dafny name: the translator has no rule for it yet.".to_string()))
            }
            Item::Function(f) => match unreadable_name(&f) {
                Some(n) => refusals.push((f.file.clone(), f.line, format!("{n}: a name with a character Dafny cannot read."))),
                None => funcs.push(f),
            },
        }
    }
    // The Dafny names, by key.
    // ponytail: a count of each plain name for each function. A file has dozens of functions. Upgrade: one pass with a map.
    let mut methods = Methods::new();
    // The functions that write their object, by the id of their keys, for the header of a method with no body.
    let mut writing = std::collections::HashSet::new();
    let mut writing_virtual = std::collections::HashSet::new();
    let mut const_void = std::collections::HashSet::new();
    // The names of the reference parameters of each function, by the id of its key, for the header of a method with no body, decision 0108.
    let mut refs: HashMap<u32, Vec<u32>> = HashMap::new();
    // The place of each function, by the id of its key, for its method header.
    let mut at = HashMap::new();
    // The file, line, name and reason of each trusted function, by the id of its key, for the report of prove.
    let mut reasons = HashMap::new();
    // A member function is named by its struct too, `Struct'name`, decision 0089. So is a constructor, whose result is `This`, decision
    // 0094. C++ cannot write `'`, so it clashes with no name.
    let plain = |f: &JFunction| match (f.params.first(), &f.ret) {
        // `this` of a virtual function of an interface names it too, decision 0165.
        (Some((_, JTy::This(k) | JTy::ThisMut(k) | JTy::Iface(k) | JTy::IfaceMut(k))), _) | (_, JTy::This(k)) => format!("{}'{}", structs.iter().find(|s| s.key == *k).map_or("", |s| s.full.as_str()), dafny_word(&f.name)),
        // A static member function has the name of its class, `Tally::bump` is `Tally'bump`, decision 0174.
        // An instance of a function template is the template, `'of'`, and the Dafny type of each argument, joined by `'`, decision 0180. A `'` never clashes.
        _ => {
            let base = operator_word(&f.name).map_or_else(|| f.name.replace("::", "'"), str::to_string);
            let word = |t: &JTy| type_word(t, &|k| structs.iter().find(|s| s.key == *k).map_or("", |s| s.full.as_str()).to_string(), &|k| enums.iter().find(|e| e.key == *k).map_or("", |e| e.name.as_str()).to_string());
            if f.of.is_empty() { base } else { format!("{base}'of'{}", f.of.iter().map(word).collect::<Vec<_>>().join("'")) }
        }
    };
    for (i, f) in funcs.iter().enumerate() {
        let same = funcs.iter().filter(|g| plain(g) == plain(f)).count();
        let k = funcs[..=i].iter().filter(|g| plain(g) == plain(f)).count();
        let dafny = if same == 1 { format!("c_{}", plain(f)) } else { format!("c_{}'{k}", plain(f)) };
        let key = names.id(&f.key);
        if f.class.is_some() {
            // The id of the qualified name, so a contract that spells it finds the member of the table, decision 0174.
            names.id(&f.name);
            names.statics.push(f.name.clone());
        }
        names.functions.insert(key, format!("{dafny}'"));
        names.fn_names.insert(key, f.name.clone());
        if let Some((_, JTy::This(k) | JTy::ThisMut(k) | JTy::Iface(k) | JTy::IfaceMut(k))) = f.params.first() {
            let class = names.id(k);
            names.fn_classes.insert(key, class);
        }
        methods.insert(key, dafny);
        if matches!(f.params.first(), Some((_, JTy::ThisMut(_) | JTy::IfaceMut(_)))) {
            writing.insert(key);
        }
        if matches!(f.params.first(), Some((_, JTy::IfaceMut(_)))) {
            writing_virtual.insert(key);
        }
        // A const virtual function that gives no value has no function and no upcast line, as one that writes its object has none, decision 0209.
        // It does not give its object back.
        if matches!(f.params.first(), Some((_, JTy::Iface(_)))) && matches!(f.ret, JTy::Void) {
            writing_virtual.insert(key);
            const_void.insert(key);
        }
        at.insert(key, names.place(&f.file, f.line));
        if let Some((reason, file, line)) = &f.trusted {
            reasons.insert(key, (file.clone(), *line, f.name.clone(), reason.clone()));
        }
    }
    // The Dafny name of each enum: `E_{plain}`, or `E_{plain}'{k}` when two enums share a plain name, decision 0109.
    let enum_places: Vec<(u32, u32)> = enums.iter().map(|en: &JEnum| (names.place(&en.file, en.line), names.id(&en.key))).collect();
    for (i, en) in enums.iter().enumerate() {
        let same = enums.iter().filter(|g| g.name == en.name).count();
        let k = enums[..=i].iter().filter(|g| g.name == en.name).count();
        let key = names.id(&en.key);
        names.datatypes.insert(key, if same == 1 { format!("E_{}", en.name) } else { format!("E_{}'{k}", en.name) });
        names.enums.push((en.name.clone(), key, en.enumerators.clone()));
    }
    // The Dafny name of each struct: `S_{plain}`, or `S_{plain}'{k}` when two structs share a plain name.
    let mut table = Structs::Nil;
    for (i, st) in structs.iter().enumerate() {
        let same = structs.iter().filter(|g| g.full == st.full).count();
        let k = structs[..=i].iter().filter(|g| g.full == st.full).count();
        let key = names.id(&st.key);
        names.datatypes.insert(key, if same == 1 { format!("S_{}", st.full) } else { format!("S_{}'{k}", st.full) });
        names.class_names.insert(key, st.name.clone());
        names.members.insert(st.key.clone(), st.members.iter().map(|(n, _)| n.clone()).collect());
        names.struct_fields.insert(st.key.clone(), st.fields.iter().filter(|(_, t)| matches!(t, JTy::Struct(_))).map(|(n, _)| n.clone()).collect());
    }
    // The classes over interfaces, by key, for the check of each override, and the interfaces of the table, decision 0165.
    let base_rows: Vec<(u32, Vec<u32>, bool)> =
        structs.iter().filter(|st| !st.bases.is_empty()).map(|st| (names.id(&st.key), st.bases.iter().map(|b| names.id(b)).collect(), st.is_final)).collect();
    let interface_flags: Vec<bool> = structs.iter().map(|st| st.interface).collect();
    // A class over an interface that is not final is no type of the model, so it has no datatype, decision 0165.
    let open_flags: Vec<bool> = structs.iter().map(|st| !st.bases.is_empty() && !st.is_final).collect();
    // An interface is named by its plain name in C++, or by its full name when two structs share the plain name, decision 0166.
    let interface_names: Vec<String> = structs
        .iter()
        .filter(|st| st.interface)
        .map(|st| if structs.iter().filter(|g| g.name == st.name).count() > 1 && !st.qualified.is_empty() { st.qualified.clone() } else { st.name.clone() })
        .collect();
    for (st, name) in structs.iter().filter(|st| st.interface).zip(&interface_names) {
        let key = names.id(&st.key);
        names.interface_names.insert(key, name.clone());
    }
    let struct_places: Vec<(u32, Option<String>)> = structs.iter().map(|st| (names.place(&st.file, st.line), unreadable_struct_name(st).map(String::from))).collect();
    for st in structs.into_iter().rev() {
        let key = names.id(&st.key);
        let place = names.place(&st.file, st.line);
        names.file = st.file;
        let fields = st.fields.into_iter().rev().fold(Params::Nil, |rest, (n, t)| Params::Cons((names.id(&n), ty(t, &mut names)), Box::new(rest)));
        // The core marks which members are pure and their types, so the shell writes `None`.
        let members = st.members.into_iter().rev().fold(Members::Nil, |rest, (n, k)| Members::Cons((names.id(&n), (names.id(&k), None)), Box::new(rest)));
        table = Structs::Cons((key, (place, fields, members)), Box::new(table));
    }
    // The free functions with a contract are one entry of the table, under a key that no C++ name can spell, decision 0176. The core marks the pure ones
    // and finds them by name, as it finds a static. A name that two of them share is left out: a contract cannot tell the overloads apart.
    let free: Vec<&JFunction> = funcs
        .iter()
        .filter(|f| f.class.is_none() && !f.conds.is_empty() && !matches!(f.params.first(), Some((n, _)) if n == "this") && !matches!(f.ret, JTy::This(_)))
        .filter(|f| funcs.iter().filter(|g| g.name == f.name).count() == 1)
        // ponytail: only a function that a contract of the file calls is listed. Decision 0176 lists each free function with a contract, but a twin and its link
        // line show the body to every caller, so each function with a contract would move the verdicts of files that never call it in a contract. Upgrade: list them all.
        .filter(|f| {
            let mut texts = Vec::new();
            funcs.iter().for_each(|g| {
                texts.extend(g.conds.iter().map(|c| c.text.as_str()));
                g.body.iter().for_each(|s| stmt_conds(s, &mut texts));
            });
            texts.iter().any(|t| calls_name(t, &f.name))
        })
        .collect();
    let file_entry = !free.is_empty();
    if file_entry {
        names.file_fns = free.iter().map(|f| f.name.clone()).collect();
        let members = free.iter().rev().fold(Members::Nil, |rest, f| Members::Cons((names.id(&f.name), (names.id(&f.key), None)), Box::new(rest)));
        table = Structs::Cons((names.id("'file"), (0, Params::Nil, members)), Box::new(table));
    }
    let count = funcs.len();
    let fns = funcs.into_iter().rev().map(|f| function(f, &mut names)).fold(Fns::Nil, |rest, f| Fns::Cons(Box::new(f), Box::new(rest)));
    // Each global that a function lists is a parameter of it, decision 0173. The core does it before it translates.
    let gs = globals.into_iter().rev().fold(Params::Nil, |rest, (n, t)| Params::Cons((names.id(&n), ty(t, &mut names)), Box::new(rest)));
    let fns = globalize(&fns, &gs);
    // The reference parameters of each function, written and implicit, by the id of its key, decision 0108.
    let mut seen_fns = &fns;
    while let List::Cons(f, next) = seen_fns {
        let mut ps = &f.params;
        let mut mutable = Vec::new();
        while let List::Cons((n, t), more) = ps {
            if matches!(t, Ty::Mut(_) | Ty::MutSeq(_)) {
                mutable.push(*n);
            }
            ps = more;
        }
        refs.insert(f.name, mutable);
        seen_fns = next;
    }
    let bases = base_rows
        .iter()
        .rev()
        .fold(List::Nil, |rest, (d, bs, fin)| List::Cons((*d, (bs.iter().rev().fold(List::Nil, |r, b| List::Cons(*b, Box::new(r))), *fin)), Box::new(rest)));
    let mut models = translate_file(&fns, &table, &bases);
    let overrides = translate_overrides(&bases, &fns, &table);
    let mut smodels = translate_structs(&table);
    // The entry of the file is no datatype, decision 0176.
    if file_entry {
        let List::Cons(_, rest) = smodels else { unreachable!("one model for each entry") };
        smodels = *rest;
    }
    // The companion file, when the scan passed it, goes after the methods. Each of its lines is a place in its own file.
    let (mut companion_text, mut companion_places) = (String::new(), Vec::new());
    if let Some((path, text)) = companion.filter(|(_, text)| companion_ok && !text.is_empty()) {
        companion_places = (1..=text.lines().count()).map(|n| Some(Line { place: names.place(path, n as u32), scope: Vec::new(), own: Vec::new() })).collect();
        companion_text = if text.ends_with('\n') { text.to_string() } else { format!("{text}\n") };
    }
    // The result type of each method, so a call that writes its object can drop the value.
    let mut rets = HashMap::new();
    let mut seen = &models;
    while let List::Cons(model, next) = seen {
        match model {
            Model::Full(m) => rets.insert(m.name, m.ret),
            Model::Bare(key, _, ret, _) => rets.insert(*key, *ret),
            Model::Refused(_) => None,
        };
        seen = next;
    }
    let mut p = Printer { copies: Vec::new(), pending: Vec::new(), method_lines: HashMap::new(), calls: HashMap::new(), owned: HashMap::new(), writing: writing_virtual, const_void, refs: refs.clone(), downs: Default::default(), names: &names, methods: &methods, rets: &rets, out: PRELUDE.to_string(), lines: Vec::new(), scope: Vec::new(), own: Vec::new(), writes: false, fresh: 0, temps: 0, in_block: false, laws: format!("{models:?}").contains("BitOp(") };
    p.lines.extend(PRELUDE.lines().map(|_| None));
    let mut refused_at = Vec::new();
    for (en, (place, key)) in enums.iter().zip(enum_places) {
        let name = &names.datatypes[&key];
        let constructors: Vec<String> = en.enumerators.iter().map(|e| format!("{name}'{e}")).collect();
        p.put(0, format!("datatype {name} = {}", constructors.join(" | ")), place);
    }
    // A `std::array` field has the type `Arr'k<T>`, one declaration for each length k, decision 0196.
    let mut lengths = std::collections::BTreeMap::new();
    let mut seen_structs = &smodels;
    for (place, _) in &struct_places {
        let List::Cons(model, rest) = seen_structs else { break };
        if let Ok((_, fields)) = model {
            let mut fields = fields;
            while let List::Cons((_, t), next) = fields {
                if let DTy::Arr(_, k) = t {
                    lengths.entry(*k).or_insert(*place);
                }
                fields = next;
            }
        }
        seen_structs = rest;
    }
    for (k, place) in lengths {
        p.put(0, format!("type Arr'{k}<T> = s: seq<T> | |s| == {k} witness *"), place);
    }
    for (((place, unreadable), interface), open) in struct_places.into_iter().zip(interface_flags).zip(open_flags) {
        let List::Cons(model, rest) = smodels else { unreachable!("one model for each struct") };
        match model {
            // The struct is refused, and its callers keep the type. The refusal stands for the file.
            Ok(_) if unreadable.is_some() => refused_at.push((place, format!("{}: a name with a character Dafny cannot read.", unreadable.unwrap_or_default()))),
            Ok(_) if open => {}
            // An interface is a type with no value that the model can see, decision 0165.
            Ok((key, List::Nil)) if interface => p.put(0, format!("type {}(==)", names.datatypes[&key]), place),
            Ok((key, List::Nil)) => p.put(0, format!("datatype {0} = {0}()", names.datatypes[&key]), place),
            Ok((key, mut fields)) => {
                let mut shown = Vec::new();
                while let List::Cons((n, t), next) = fields {
                    // ponytail: the type of the elements is keyed by the field name. Two structs with one field name and two element types clash. Upgrade: key it by the struct.
                    if matches!(t, DTy::Seq(Scalar::Own(_))) {
                        p.note(n, t);
                    }
                    shown.push(format!("f_{}: {}", names.text(n), dty(t, &names)));
                    fields = *next;
                }
                p.put(0, format!("datatype {0} = {0}({1})", names.datatypes[&key], shown.join(", ")), place);
            }
            Err(r) => refused_at.push(sentence(r, &names)),
        }
        smodels = *rest;
    }
    let mut printed = 0;
    let mut trusted = Vec::new();
    let mut lemmas = Vec::new();
    let mut upcast_printed = std::collections::HashSet::new();
    // The checks by the key of the function of the override.
    let mut checks: HashMap<u32, Vec<(&DUpcast, &DOverride)>> = HashMap::new();
    let mut seen_upcasts = &overrides;
    while let List::Cons(result, next) = seen_upcasts {
        if let Ok(up) = result {
            let mut os = &up.overrides;
            while let List::Cons(o, more) = os {
                checks.entry(o.derived).or_default().push((up, o));
                os = more;
            }
        }
        seen_upcasts = next;
    }
    for _ in 0..count {
        let List::Cons(model, rest) = models else { unreachable!("one model for each function") };
        let refused = match model {
            Model::Full(m) => {
                p.method(&m, at[&m.name]);
                // The check of each override against the contract of its interface follows the method of the override, decision 0165. The upcast of a class comes
                // with the check of its first override.
                for (up, o) in checks.get(&m.name).into_iter().flatten() {
                    if upcast_printed.insert((up.derived, up.base)) {
                        p.upcast_function(up, at[&o.derived]);
                    }
                    let of = format!("{}::{}", names.class_names[&up.base], names.fn_names[&o.base]);
                    lemmas.push(p.lemma(up, o, at[&o.derived], of));
                }
                printed += 1;
                trusted.extend(reasons.remove(&m.name).filter(|_| m.trusted));
                None
            }
            Model::Bare(key, params, ret, r) => {
                // The type of each reference parameter is its type in the header.
                let outs: Vec<(u32, DTy)> = dparams(&params).into_iter().filter(|(n, _)| refs[&key].contains(n)).collect();
                p.header(key, &params, ret, (writing.contains(&key), false), &outs, at[&key]);
                printed += 1;
                Some(r)
            }
            Model::Refused(r) => Some(r),
        };
        refused_at.extend(refused.map(|r| sentence(r, &names)));
        models = *rest;
    }
    // A class that cannot be checked is refused at its line, decision 0165.
    let mut seen_checks = &overrides;
    while let List::Cons(result, next) = seen_checks {
        if let Err(r) = result {
            refused_at.push(sentence(*r, &names));
        }
        seen_checks = next;
    }
    // ponytail: a method that names `shr` is a method that shifts. Upgrade: a flag that the printer sets.
    if p.out.contains("shr(") {
        p.out.push_str(SHR);
        p.lines.extend(SHR.lines().map(|_| None));
    }
    // ponytail: a model has a bit operator when its debug text names `BitOp(`. Upgrade: a walk over the models.
    if p.laws {
        p.out.push_str(BITS);
        p.lines.extend(BITS.lines().map(|_| None));
    }
    // The model of a double operation is the file `Double.dfy` as it is, decision 0154, and the names of the module are in scope. It follows the
    // methods that name it, as `shr` does.
    let rounds = names.rounds.get();
    if names.double.get() {
        for text in [DOUBLE, "import opened Double\n"] {
            p.out.push_str(text);
            p.lines.extend(text.lines().map(|_| None));
        }
    }
    // The model of `std::sort` is the file `Algorithm.dfy` as it is, decision 0161, with the module in scope.
    if names.sorted.get() {
        for text in [ALGORITHM, "import opened Algorithm\n"] {
            p.out.push_str(text);
            p.lines.extend(text.lines().map(|_| None));
        }
    }
    // The companion file follows the methods, so none of its comments reaches a method, decision 0083.
    let start = p.lines.len();
    p.lines.extend(companion_places);
    p.out.push_str(&companion_text);
    let companion_lines = start..p.lines.len();
    // The lines of the file are those of the Dafny text from `start + 1`. Nothing is printed when the scan refused the file.
    let decls = if companion_ok { decls.into_iter().map(|(n, lemma)| (start + n, lemma)).collect() } else { Vec::new() };
    let downs: Vec<(String, String)> = p.downs.iter().map(|(d, b)| (names.class_names[d].clone(), names.class_names[b].clone())).collect();
    let (dafny, lines, copies) = (p.out, p.lines, p.copies);
    for (place, sentence) in refused_at {
        let (file, line) = names.places[place as usize].clone();
        refusals.push((file, line, sentence));
    }
    // The guard of decision 0130. Today a drop always comes with the refusal of its struct or enum, so no test reaches it. A function that the model
    // leaves out must never leave the file unrefused.
    if let (true, Some((file, line))) = (refusals.is_empty(), first_dropped) {
        refusals.push((file, line, "the model left out this function, and nothing else refused the file.".to_string()));
    }
    refusals.sort();
    refusals.dedup();
    Ok(Translation { dafny, methods: printed, trusted, refusals, rounds, exact: names.exact.get(), sorted: names.sorted.get(), interfaces: interface_names, downs, map: Map { lines, companion: companion_lines, decls, places: names.places, contracts: names.contracts, lemmas, copies } })
}
