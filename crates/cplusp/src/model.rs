//! The shell side of the translator, decisions 0056, 0057 and 0124. It reads the plugin's lines of JSON, numbers the names, hands the core the
//! bytes of each contract line and its tables, and prints the Dafny text of what the core gives back. Every rule of the translation is
//! in `cplusp_core`. Nothing here decides what is allowed.

use std::collections::HashMap;
use std::fmt::Write;

use anyhow::{Context, Result};
use cplusp_core::companion::CompanionRefusal;
use cplusp_core::contract::{LexKind, NumberFault};
use cplusp_core::model::{
    parse_contract, translate_structs, translate_unit, Args, BinOp, CastKind, CondKind, Conds, DArgs, DConds, DExpr, DParams, DStmt, DStmts, DTy, Expr, Extent, Fns,
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
    /// A local `std::vector<T>` that the function owns, decision 0160.
    Vec(JScalar),
    /// An enum class of the file by its key, decision 0109.
    Enum(String),
    Opt(JScalar),
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
}

#[derive(Deserialize)]
enum JCast {
    Read,
    NoOp,
    Construct,
    Integral(JTy, JTy),
    Other(String),
}

#[derive(Deserialize)]
enum JExpr {
    Lit(u64, JTy),
    Bool(bool),
    Var(String, JTy),
    Bin(JOp, Box<JExpr>, Box<JExpr>),
    Divide(JOp, Box<JExpr>, Box<JExpr>, JTy),
    Shr(Box<JExpr>, Box<JExpr>, JTy),
    /// An enumerator by the key of its enum and its place, decision 0109.
    Enumerator(String, u32),
    Not(Box<JExpr>),
    Neg(Box<JExpr>),
    Cast(JCast, Box<JExpr>),
    Paren(Box<JExpr>),
    Brace(Box<JExpr>),
    Size(Box<JExpr>),
    Empty(Box<JExpr>),
    Subspan(Box<JExpr>, Box<JExpr>),
    Copy(Box<JExpr>, JTy, JTy),
    Field(Box<JExpr>, String),
    HasValue(Box<JExpr>),
    Value(Box<JExpr>),
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
    /// `v.push_back(e)` where `v` is a vector by reference, decision 0148.
    PushBack(String, JExpr, u32),
    /// `p.f = e` where `p` is a reference parameter, decision 0108.
    SetRefField(String, String, JExpr, u32),
    /// A switch over an enum, decision 0109: its condition, the key of the enum, the cases as (place of the enumerator, statements), and the line.
    Switch(JExpr, String, Vec<(u32, Vec<JStmt>)>, u32),
    Call(String, String, Vec<JExpr>, u32),
    Exit(u32),
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
    /// The constants of the file that C++ does not find from the function, decision 0107. They hide no constant from `shadow`, they join it.
    #[serde(default)]
    hidden: Vec<String>,
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
    /// The functions that the companion file declares. Empty when there is no file or the scan refused it, decision 0079.
    declared: Vec<String>,
    /// The lemmas that the companion file declares, apart from the functions, decision 0099.
    lemmas: Vec<String>,
    /// The sentence of a body line that the core refuses as `Syntax`, by the place of the line.
    said: HashMap<u32, String>,
    /// The first call to an undeclared name in a contract line, by the place of the line.
    bad_calls: HashMap<u32, String>,
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
        JTy::Ptr(s) => Ty::Ptr(scalar(s, names)),
        JTy::Own(s) => Ty::Own(scalar(s, names)),
        JTy::Struct(k) => Ty::Struct(names.id(&k)),
        JTy::Mut(s) => Ty::Mut(scalar(s, names)),
        JTy::MutSeq(s) => Ty::MutSeq(scalar(s, names)),
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
    }
}

fn expr(e: JExpr, names: &mut Names) -> Expr {
    match e {
        JExpr::Lit(n, t) => Expr::Lit(n, ty(t, names)),
        JExpr::Bool(b) => Expr::Bool(b),
        JExpr::RealLit(d, k) => Expr::RealLit(d, k),
        JExpr::Ratio(m, q) => Expr::Ratio(m, q),
        JExpr::Var(v, t) => Expr::Var(names.id(&v), ty(t, names)),
        JExpr::Bin(o, a, b) => Expr::Bin(op(o), Box::new(expr(*a, names)), Box::new(expr(*b, names))),
        JExpr::Divide(o, a, b, t) => Expr::Divide(op(o), Box::new(expr(*a, names)), Box::new(expr(*b, names)), ty(t, names)),
        JExpr::Shr(a, b, t) => Expr::Shr(Box::new(expr(*a, names)), Box::new(expr(*b, names)), ty(t, names)),
        JExpr::Enumerator(k, i) => Expr::Enumerator(names.id(&k), i),
        JExpr::Not(a) => Expr::Not(Box::new(expr(*a, names))),
        JExpr::Neg(a) => Expr::Neg(Box::new(expr(*a, names))),
        JExpr::Cast(k, a) => {
            let kind = match k {
                JCast::Read => CastKind::Read,
                JCast::NoOp => CastKind::NoOp,
                JCast::Construct => CastKind::Construct,
                JCast::Integral(from, to) => CastKind::Integral(ty(from, names), ty(to, names)),
                JCast::Other(s) => CastKind::Other(names.id(&s)),
            };
            Expr::Cast(kind, Box::new(expr(*a, names)))
        }
        JExpr::Paren(a) => Expr::Paren(Box::new(expr(*a, names))),
        JExpr::Brace(a) => Expr::Brace(Box::new(expr(*a, names))),
        JExpr::Size(a) => Expr::Size(Box::new(expr(*a, names))),
        JExpr::Empty(a) => Expr::Empty(Box::new(expr(*a, names))),
        JExpr::Subspan(a, k) => Expr::Subspan(Box::new(expr(*a, names)), Box::new(expr(*k, names))),
        JExpr::Copy(a, from, to) => Expr::Copy(Box::new(expr(*a, names)), ty(from, names), ty(to, names)),
        JExpr::Field(a, f) => Expr::Field(Box::new(expr(*a, names)), names.id(&f)),
        JExpr::HasValue(a) => Expr::HasValue(Box::new(expr(*a, names))),
        JExpr::Value(a) => Expr::Value(Box::new(expr(*a, names))),
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
        JStmt::PushBack(v, e, line) => Stmt::PushBack(names.id(&v), expr(e, names), names.here(line)),
        JStmt::Switch(e, k, cases, line) => {
            let place = names.here(line);
            let key = names.id(&k);
            let cases = cases.into_iter().rev().fold(List::Nil, |rest, (i, body)| List::Cons((i, Box::new(stmts(body, names))), Box::new(rest)));
            Stmt::Switch(expr(e, names), key, Box::new(cases), place)
        }
        JStmt::SetRefField(p, f, e, line) => Stmt::SetRefField(names.id(&p), names.id(&f), expr(e, names), names.here(line)),
        JStmt::Call(key, name, args, line) => {
            let args: Vec<Expr> = args.into_iter().map(|a| expr(a, names)).collect();
            let args = args.into_iter().rev().fold(Args::Nil, |rest, a| Args::Cons(Box::new(a), Box::new(rest)));
            Stmt::Call(names.id(&key), names.id(&name), Box::new(args), names.here(line))
        }
        JStmt::Exit(line) => Stmt::Exit(names.here(line)),
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
        if !names.lemmas.iter().any(|l| l == head) {
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
    cplusp_core::contract::lex_contract(&bytes)
        .into_iter()
        .map(|lexeme| {
            let word = &text[lexeme.start..lexeme.end];
            match lexeme.kind {
                LexKind::Name(call) => {
                    // A name followed by `(` is a call, and the companion file must declare it. A member name in a member function may be a call of
                    // the member, and the core decides, decision 0090.
                    if call && !names.declared.iter().any(|d| d == word) && !names.this_members.iter().any(|d| d == word) && !names.functors.iter().any(|d| d == word) {
                        names.bad_calls.entry(line).or_insert_with(|| word.to_string());
                    }
                    Tok::Ident(names.id(word))
                }
                LexKind::Field => Tok::Field(names.id(&word[1..])),
                LexKind::Fixed(tok) => tok,
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
    cplusp_core::fold::fold(&toks, &folds)
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
        } else if c.kind == "modifies" {
            // `//@ modifies a, b` is one line for each name, decision 0108. A name may have parts, `Tally::count_`, and the core refuses it as no reference
            // parameter, decision 0110. A line of any other form is one that names no name, and the core refuses it as a form it cannot read.
            let word = |w: &str| w.starts_with(|ch: char| ch.is_ascii_alphabetic() || ch == '_') && w.chars().all(|ch| ch.is_ascii_alphanumeric() || ch == '_');
            let listed: Vec<&str> = c.text.split(',').map(str::trim).collect();
            if listed.iter().all(|n| n.split("::").all(word)) {
                listed.into_iter().map(|n| (CondKind::Modifies, Expr::Name(names.id(n)))).collect()
            } else {
                vec![(CondKind::Modifies, Expr::Int(0))]
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
        JExpr::Var(v, _) => out.push(v),
        JExpr::Bin(_, a, b) | JExpr::Divide(_, a, b, _) | JExpr::Shr(a, b, _) | JExpr::Index(a, b) | JExpr::Subspan(a, b) => {
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
        JExpr::Not(a) | JExpr::Neg(a) | JExpr::Cast(_, a) | JExpr::Paren(a) | JExpr::Brace(a) | JExpr::Size(a) | JExpr::Empty(a) | JExpr::Copy(a, ..) | JExpr::Field(a, _) | JExpr::HasValue(a) | JExpr::Value(a) | JExpr::Wrap(a) => expr_names(a, out),
        JExpr::Call(_, _, args, _) | JExpr::Construct(_, args) => args.iter().for_each(|a| expr_names(a, out)),
        JExpr::Lit(..) | JExpr::Bool(_) | JExpr::RealLit(..) | JExpr::Ratio(..) | JExpr::Nullopt | JExpr::Enumerator(..) | JExpr::Unknown(..) => {}
    }
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
        JStmt::SetField(_, e, _) => expr_names(e, out),
        JStmt::PushBack(v, e, _) => {
            out.push(v);
            expr_names(e, out);
        }
        JStmt::SetIndex(v, i, e, _) => {
            out.push(v);
            expr_names(i, out);
            expr_names(e, out);
        }
        JStmt::Switch(e, _, cases, _) => {
            expr_names(e, out);
            cases.iter().flat_map(|(_, body)| body).for_each(|s| stmt_names(s, out));
        }
        JStmt::SetRefField(p, _, e, _) => {
            out.push(p);
            expr_names(e, out);
        }
        JStmt::Call(_, _, args, _) => args.iter().for_each(|a| expr_names(a, out)),
        JStmt::Exit(_) | JStmt::Assert(_) | JStmt::Apply(_) => {}
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
    let mut names = vec![dafny_word(&f.name)];
    names.extend(f.params.iter().map(|(n, _)| n.as_str()));
    f.body.iter().for_each(|s| stmt_names(s, &mut names));
    names.into_iter().find(|n| !readable(n))
}

/// `operator()` is a name of C++ that the Dafny text prints as `call`, decision 0098. Every other name stays as it is.
fn dafny_word(name: &str) -> &str {
    if name == "operator()" {
        "call"
    } else {
        name
    }
}

fn readable(name: &str) -> bool {
    name.chars().all(|c| c.is_ascii_alphanumeric() || c == '_')
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
    names.shadow = f.params.iter().map(|(n, _)| n.clone()).chain(f.hidden.iter().cloned()).collect();
    let mut used = Vec::new();
    f.body.iter().for_each(|s| stmt_names(s, &mut used));
    names.shadow.extend(used.into_iter().map(str::to_string));
    // The names that a contract may call as a functor, decision 0098.
    names.functors = f.params.iter().filter(|(_, t)| matches!(t, JTy::Struct(_))).map(|(n, _)| n.clone()).collect();
    if let (Some((_, JTy::This(k) | JTy::ThisMut(k))), _) | (_, JTy::This(k)) = (f.params.first(), &f.ret) {
        names.functors.extend(names.struct_fields.get(k).cloned().unwrap_or_default());
    }
    // A constructor reads the members of the value it builds, decision 0094.
    names.this_members = match (f.params.first(), &f.ret) {
        (Some((_, JTy::This(k) | JTy::ThisMut(k))), _) | (_, JTy::This(k)) => names.members.get(k).cloned().unwrap_or_default(),
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
    Function { name, line, params, ret, trusted: f.trusted.is_some(), conds: conds(f.conds, names), body: stmts(f.body, names) }
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
type Vec<T> = s: seq<T> | |s| < 0x1_0000_0000_0000_0000 witness []
function trunc_size(x: int): nat { if x < 0 then -x else x }
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
";

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

fn dscalar(s: Scalar, names: &Names) -> String {
    match s {
        Scalar::I32 => "int32".to_string(),
        Scalar::I64 => "int64".to_string(),
        Scalar::U8 => "uint8".to_string(),
        Scalar::U32 => "uint32".to_string(),
        Scalar::U64 => "uint64".to_string(),
        Scalar::Bool => "bool".to_string(),
        Scalar::Struct(k) => names.datatypes[&k].clone(),
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
        DTy::Struct(k) | DTy::Enum(k) => names.datatypes[&k].clone(),
        DTy::Opt(s) => format!("Option<{}>", dscalar(s, names)),
        // A method that gives no value has no `result`, so no caller prints this type.
        DTy::Void => String::new(),
    }
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
    }
}

/// The one mangling of a C++ variable for Dafny, for code and contract alike. The prefix `v_` keeps a name clear of the words Dafny
/// reserves, such as `old` and `function`, and of `result`. The contract word `result` is no name: it is `Tok::Result`, and prints as
/// `result`. A method has the prefix `c_`, so a variable never hides a method, decision 0060.
// An unnamed parameter is `v_'N` and an overload is `c_{plain}'{k}`. C++ cannot write `'` in a name, so no clash is possible.
fn mangle(name: &str) -> String {
    format!("v_{name}")
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
        DExpr::Nothing => "None".to_string(),
        DExpr::Just(a) => format!("Some({})", dexpr(a, names)),
        DExpr::Enumerator(k, i) => format!("{}'{}", names.datatypes[k], names.enums.iter().find(|e| e.1 == *k).and_then(|e| e.2.get(*i as usize)).map_or("'unknown", String::as_str)),
        DExpr::Ctor(k, args) => format!("{}({})", names.datatypes[k], dargs(args, names).join(", ")),
        DExpr::Len(a) => format!("|{}|", dexpr(a, names)),
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
    pub map: Map,
}

/// The printer of the Dafny text. It writes one line at a time, and keeps the map for each line it writes.
struct Printer<'a> {
    names: &'a Names,
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
    fn update(&self, objs: &Objs, m: u32, args: &DArgs) -> (String, String) {
        let mut places = Vec::new();
        let mut rest = objs;
        while let List::Cons(o, next) = rest {
            places.push(match o {
                Obj::Local(n) => mangle(self.names.text(*n)),
                Obj::Object => "v_this'".to_string(),
                Obj::Out(x) => format!("{}'", mangle(self.names.text(*x))),
            });
            rest = next;
        }
        (places.join(", "), self.call(m, args))
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
            DStmt::Update(objs, m, args) => {
                let (object, call) = self.update(objs, *m, args);
                match self.rets.get(m) {
                    Some(DTy::Void) | None => self.put(depth, format!("{object} := {call};"), place),
                    // The value is dropped into a fresh local.
                    Some(t) => {
                        self.fresh += 1;
                        let r = format!("v_'r{}", self.fresh);
                        self.put(depth, format!("var {r}: {}; {r}, {object} := {call};", dty(*t, names)), place);
                    }
                }
            }
            DStmt::LocalUpdate(x, t, objs, m, args) => {
                let (object, call) = self.update(objs, *m, args);
                let x = mangle(names.text(*x));
                self.put(depth, format!("var {x}: {}; {x}, {object} := {call};", dty(*t, names)), place);
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
                let base = self.temps;
                let outer = names.temp_base.replace(Some(base));
                let mut rest = calls;
                while let List::Cons((t, ty, m, args), next) = rest {
                    let call = self.call(*m, args);
                    self.put(depth, format!("var v_'t{}: {} := {call};", base + t, dty(*ty, names)), place);
                    self.temps = self.temps.max(base + t + 1);
                    rest = next;
                }
                self.stmt(inner, place, depth);
                names.temp_base.set(outer);
            }
            DStmt::Assert(e) => self.put(depth, format!("assert {};", dexpr(e, names)), place),
            DStmt::Apply(l, args) => self.put(depth, format!("{}({});", names.text(*l), dargs(args, names).join(", ")), place),
            // A local vector is a plain `seq`, because `push_back` may grow it past the bound of `Vec`, as for a vector given back, decision 0160.
            DStmt::Local(x, t, e) => {
                let shown = match t {
                    DTy::Seq(s) => format!("seq<{}>", dscalar(*s, names)),
                    _ => dty(*t, names),
                };
                self.put(depth, format!("var {}: {} := {};", mangle(names.text(*x)), shown, dexpr(e, names)), place)
            }
            DStmt::LocalCall(x, t, m, args) => {
                let call = self.call(*m, args);
                self.put(depth, format!("var {}: {} := {call};", mangle(names.text(*x)), dty(*t, names)), place);
            }
            DStmt::ReturnCall(m, args) => {
                let call = self.call(*m, args);
                self.put(depth, format!("result := {call};"), place);
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
        self.out.push('\n');
        self.lines.push(None);
        self.put(0, format!("function {}({}): {}", self.names.functions[&m.name], shown.join(", "), dty(m.ret, self.names)), place);
        let mut cs = &m.requires;
        while let List::Cons((e, line), next) = cs {
            self.put(1, format!("requires {}", dexpr(e, self.names)), *line);
            self.scope.push(*line);
            cs = next;
        }
        self.put(0, "{".to_string(), place);
        self.put(1, dexpr(body, self.names), place);
        self.put(0, "}".to_string(), place);
        self.scope.clear();
    }

    fn method(&mut self, m: &Method, place: u32) {
        if let Some(body) = &m.function {
            self.function(m, body, place);
        }
        let outs = dparams(&m.outs);
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
            return;
        }
        self.put(0, "{".to_string(), place);
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
    }
}

/// A refusal as the place it points at and the sentence the bot reads.
fn sentence(r: Refusal, names: &Names) -> (u32, String) {
    match r {
        Refusal::Construct(k, line) => (line, format!("{}: the translator has no rule for it yet.", names.text(k))),
        Refusal::Name(n, line) => (line, format!("{} in the contract is no parameter.", names.text(n))),
        Refusal::NoField(f, line) => (line, format!("{} in the contract is no field of the struct.", names.text(f))),
        Refusal::NotPure(n, line) => (line, format!("{} is no pure member function of its struct.", names.text(n))),
        Refusal::Syntax(line) if names.bad_calls.contains_key(&line) => (line, format!("{} is no function of the companion file.", names.bad_calls[&line])),
        Refusal::Syntax(line) if names.said.contains_key(&line) => (line, names.said[&line].clone()),
        Refusal::Syntax(line) => (line, "the contract line has a form the translator cannot read.".to_string()),
        Refusal::Backslash(line) => (line, "a contract line that ends in a backslash.".to_string()),
        Refusal::Callee(n, line) => (line, format!("a call to {}, which has no model in view.", names.text(n))),
        Refusal::Place(line) => (
            line,
            "a call out of place. The translator takes a call when C++ runs it once and the statement uses its value. It takes a call that writes a value back or gives no value only alone.".to_string(),
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
        Refusal::HoldsSeq(line) => (line, "a struct that holds a sequence is in the subset only as a parameter.".to_string()),
        Refusal::Element(line) => (line, "an optional of a struct or a sequence of bool has no rule yet.".to_string()),
        Refusal::Extent(line) => (line, "a sequence or an optional made from one of another type or length.".to_string()),
        Refusal::NoTarget(line) => (line, "the call writes a value back, and the translator writes back only to a local or a reference parameter.".to_string()),
        Refusal::NoObject(n, line) => (line, format!("{} is a member of the struct. A requires line of a constructor has no object yet.", names.text(n))),
        Refusal::IndexName(n, line) => (line, format!("{} on the index line is a name the function already has.", names.text(n))),
        Refusal::Rounds(line) => (line, "a double operation rounds, and the translator has no rule for it yet.".to_string()),
        Refusal::Finite(n, line) if names.text(n).starts_with('\'') => (line, "a double parameter has no name. Give it a name and say std::isfinite of it in a requires line.".to_string()),
        Refusal::Finite(n, line) => (line, format!("{} is a double. A requires line needs std::isfinite({}).", names.text(n), names.text(n))),
        Refusal::FiniteResult(line) => (line, "a trusted function that gives a double needs std::isfinite(result) in an ensures line.".to_string()),
        Refusal::VecLocal(line) => (line, "a local vector has a rule only as a copy of a vector in scope.".to_string()),
        Refusal::PassLocal(n, line) => (line, format!("{} is a local vector. A call that passes it by reference has no rule yet.", names.text(n))),
        Refusal::PassOn(n, line) => (line, format!("{} is a vector by reference. A call that passes it on has no rule yet.", names.text(n))),
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
    // The text `operator()` is the first word, so its id is `CALL_OP`, the id that the core uses, decision 0098.
    let mut names = Names { words: vec!["operator()".to_string()], ..Default::default() };
    let mut refusals = Vec::new();
    let mut funcs = Vec::new();
    let mut structs = Vec::new();
    let mut enums = Vec::new();
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
    // A function that names a struct or an enum refused for its name has no method, with no refusal of its own.
    let mut unreadable_keys: Vec<String> = items
        .iter()
        .filter_map(|(i, _)| match i {
            Item::Struct(st) => unreadable_struct_name(st).map(|_| &st.key),
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
            Item::Constant { constant, value } => names.constants.extend(value.parse().ok().map(|v| (constant, v))),
            Item::Real { constant, real } => names.reals.push((constant, real.0, real.1, real.2)),
            Item::Enum(en) => match unreadable_enum_name(&en) {
                Some(n) => refusals.push((en.file.clone(), en.line, format!("{n}: a name with a character Dafny cannot read."))),
                None => enums.push(en),
            },
            Item::Struct(st) if dropped.contains(&st.key) => {
                first_dropped.get_or_insert((st.file.clone(), st.line));
            }
            Item::Struct(st) => structs.push(st),
            Item::Function(f) if unreadable_keys.iter().any(|k| l.contains(k.as_str())) => {
                first_dropped.get_or_insert((f.file.clone(), f.line));
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
    // The names of the reference parameters of each function, by the id of its key, for the header of a method with no body, decision 0108.
    let mut refs: HashMap<u32, Vec<u32>> = HashMap::new();
    // The place of each function, by the id of its key, for its method header.
    let mut at = HashMap::new();
    // The file, line, name and reason of each trusted function, by the id of its key, for the report of prove.
    let mut reasons = HashMap::new();
    // A member function is named by its struct too, `Struct'name`, decision 0089. So is a constructor, whose result is `This`, decision
    // 0094. C++ cannot write `'`, so it clashes with no name.
    let plain = |f: &JFunction| match (f.params.first(), &f.ret) {
        (Some((_, JTy::This(k) | JTy::ThisMut(k))), _) | (_, JTy::This(k)) => format!("{}'{}", structs.iter().find(|s| s.key == *k).map_or("", |s| s.name.as_str()), dafny_word(&f.name)),
        _ => f.name.clone(),
    };
    for (i, f) in funcs.iter().enumerate() {
        let same = funcs.iter().filter(|g| plain(g) == plain(f)).count();
        let k = funcs[..=i].iter().filter(|g| plain(g) == plain(f)).count();
        let dafny = if same == 1 { format!("c_{}", plain(f)) } else { format!("c_{}'{k}", plain(f)) };
        let key = names.id(&f.key);
        names.functions.insert(key, format!("{dafny}'"));
        methods.insert(key, dafny);
        if matches!(f.params.first(), Some((_, JTy::ThisMut(_)))) {
            writing.insert(key);
        }
        let mutable: Vec<u32> = f.params.iter().enumerate().filter(|(_, (_, t))| matches!(t, JTy::Mut(_) | JTy::MutSeq(_))).map(|(i, (n, _))| names.id(&if n.is_empty() { format!("'{i}") } else { n.clone() })).collect();
        refs.insert(key, mutable);
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
        let same = structs.iter().filter(|g| g.name == st.name).count();
        let k = structs[..=i].iter().filter(|g| g.name == st.name).count();
        let key = names.id(&st.key);
        names.datatypes.insert(key, if same == 1 { format!("S_{}", st.name) } else { format!("S_{}'{k}", st.name) });
        names.members.insert(st.key.clone(), st.members.iter().map(|(n, _)| n.clone()).collect());
        names.struct_fields.insert(st.key.clone(), st.fields.iter().filter(|(_, t)| matches!(t, JTy::Struct(_))).map(|(n, _)| n.clone()).collect());
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
    let count = funcs.len();
    let fns = funcs.into_iter().rev().map(|f| function(f, &mut names)).fold(Fns::Nil, |rest, f| Fns::Cons(Box::new(f), Box::new(rest)));
    let mut models = translate_unit(&fns, &table);
    let mut smodels = translate_structs(&table);
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
    let mut p = Printer { names: &names, methods: &methods, rets: &rets, out: PRELUDE.to_string(), lines: Vec::new(), scope: Vec::new(), own: Vec::new(), writes: false, fresh: 0, temps: 0 };
    p.lines.extend(PRELUDE.lines().map(|_| None));
    let mut refused_at = Vec::new();
    for (en, (place, key)) in enums.iter().zip(enum_places) {
        let name = &names.datatypes[&key];
        let constructors: Vec<String> = en.enumerators.iter().map(|e| format!("{name}'{e}")).collect();
        p.put(0, format!("datatype {name} = {}", constructors.join(" | ")), place);
    }
    for (place, unreadable) in struct_places {
        let List::Cons(model, rest) = smodels else { unreachable!("one model for each struct") };
        match model {
            // The struct is refused, and its callers keep the type. The refusal stands for the file.
            Ok(_) if unreadable.is_some() => refused_at.push((place, format!("{}: a name with a character Dafny cannot read.", unreadable.unwrap_or_default()))),
            Ok((key, List::Nil)) => p.put(0, format!("datatype {0} = {0}()", names.datatypes[&key]), place),
            Ok((key, mut fields)) => {
                let mut shown = Vec::new();
                while let List::Cons((n, t), next) = fields {
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
    for _ in 0..count {
        let List::Cons(model, rest) = models else { unreachable!("one model for each function") };
        let refused = match model {
            Model::Full(m) => {
                p.method(&m, at[&m.name]);
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
    // ponytail: a method that names `shr` is a method that shifts. Upgrade: a flag that the printer sets.
    if p.out.contains("shr(") {
        p.out.push_str(SHR);
        p.lines.extend(SHR.lines().map(|_| None));
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
    // The companion file follows the methods, so none of its comments reaches a method, decision 0083.
    let start = p.lines.len();
    p.lines.extend(companion_places);
    p.out.push_str(&companion_text);
    let companion_lines = start..p.lines.len();
    // The lines of the file are those of the Dafny text from `start + 1`. Nothing is printed when the scan refused the file.
    let decls = if companion_ok { decls.into_iter().map(|(n, lemma)| (start + n, lemma)).collect() } else { Vec::new() };
    let (dafny, lines) = (p.out, p.lines);
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
    Ok(Translation { dafny, methods: printed, trusted, refusals, rounds, exact: names.exact.get(), map: Map { lines, companion: companion_lines, decls, places: names.places, contracts: names.contracts } })
}
