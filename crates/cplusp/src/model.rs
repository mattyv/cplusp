//! The shell side of the translator, decisions 0056 and 0057. It reads the plugin's lines of JSON, numbers the names, cuts the contract
//! lines into tokens, hands the core its types, and prints the Dafny text of what the core gives back. Every rule of the translation is
//! in `cplusp_core::model`. Nothing here decides what is allowed.

use std::collections::HashMap;
use std::fmt::Write;

use anyhow::{Context, Result};
use cplusp_core::model::{
    parse_contract, translate_structs, translate_unit, Args, BinOp, CastKind, CondKind, Conds, DArgs, DConds, DExpr, DParams, DStmt, DStmts, DTy, Expr, Extent, Fns,
    Function, Method, Model, Models, Names as CNames, Params, Refusal, Scalar, Stmt, Stmts, StructModels, Structs, Tok, Ty,
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
}

#[derive(Deserialize)]
enum JTy {
    I32,
    I64,
    U8,
    U32,
    U64,
    Bool,
    Seq(JScalar, Option<u64>),
    Struct(String),
    Other(String),
}

#[derive(Deserialize)]
enum JOp {
    Add,
    Sub,
    Mul,
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
    Not(Box<JExpr>),
    Neg(Box<JExpr>),
    Cast(JCast, Box<JExpr>),
    Paren(Box<JExpr>),
    Brace(Box<JExpr>),
    Size(Box<JExpr>),
    Copy(Box<JExpr>, JTy, JTy),
    Field(Box<JExpr>, String),
    Construct(String, Vec<JExpr>),
    Index(Box<JExpr>, Box<JExpr>),
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
    While(JExpr, Vec<JCond>, Vec<JStmt>, u32),
    For(Box<JStmt>, JExpr, Box<JStmt>, Vec<JCond>, Vec<JStmt>, u32),
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
    Orphan { orphan: u32, file: String },
    Struct(JStruct),
    Function(JFunction),
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
}

#[derive(Deserialize)]
struct JFunction {
    key: String,
    name: String,
    file: String,
    line: u32,
    params: Vec<(String, JTy)>,
    ret: JTy,
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
}

impl Names {
    fn id(&mut self, s: &str) -> u32 {
        let at = self.words.iter().position(|n| n == s).unwrap_or_else(|| {
            self.words.push(s.to_string());
            self.words.len() - 1
        });
        at as u32
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

fn ty(t: JTy, names: &mut Names) -> Ty {
    match t {
        JTy::I32 => Ty::I32,
        JTy::I64 => Ty::I64,
        JTy::U8 => Ty::U8,
        JTy::U32 => Ty::U32,
        JTy::U64 => Ty::U64,
        JTy::Bool => Ty::Bool,
        JTy::Seq(s, extent) => Ty::Seq(match s {
            JScalar::I32 => Scalar::I32,
            JScalar::I64 => Scalar::I64,
            JScalar::U8 => Scalar::U8,
            JScalar::U32 => Scalar::U32,
            JScalar::U64 => Scalar::U64,
            JScalar::Bool => Scalar::Bool,
        }, extent.map_or(Extent::Dynamic, Extent::Fixed)),
        JTy::Struct(k) => Ty::Struct(names.id(&k)),
        JTy::Other(s) => Ty::Other(names.id(&s)),
    }
}

fn op(o: JOp) -> BinOp {
    match o {
        JOp::Add => BinOp::Add,
        JOp::Sub => BinOp::Sub,
        JOp::Mul => BinOp::Mul,
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
        JExpr::Var(v, t) => Expr::Var(names.id(&v), ty(t, names)),
        JExpr::Bin(o, a, b) => Expr::Bin(op(o), Box::new(expr(*a, names)), Box::new(expr(*b, names))),
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
        JExpr::Copy(a, from, to) => Expr::Copy(Box::new(expr(*a, names)), ty(from, names), ty(to, names)),
        JExpr::Field(a, f) => Expr::Field(Box::new(expr(*a, names)), names.id(&f)),
        JExpr::Construct(k, args) => {
            let args: Vec<Expr> = args.into_iter().map(|a| expr(a, names)).collect();
            let args = args.into_iter().rev().fold(Args::Nil, |rest, a| Args::Cons(Box::new(a), Box::new(rest)));
            Expr::Construct(names.id(&k), Box::new(args))
        }
        JExpr::Index(a, i) => Expr::Index(Box::new(expr(*a, names)), Box::new(expr(*i, names))),
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
        JStmt::While(c, cs, body, line) => Stmt::While(expr(c, names), Box::new(conds(cs, names)), Box::new(stmts(body, names)), names.here(line)),
        JStmt::For(init, c, step, cs, body, line) => {
            let init = Box::new(stmt(*init, names));
            let c = expr(c, names);
            Stmt::For(init, c, Box::new(stmt(*step, names)), Box::new(conds(cs, names)), Box::new(stmts(body, names)), names.here(line))
        }
        JStmt::Unknown(k, line) => Stmt::Unknown(names.id(&k), names.here(line)),
    }
}

/// A cons list from a vector.
fn stmts(v: Vec<JStmt>, names: &mut Names) -> Stmts {
    let items: Vec<Stmt> = v.into_iter().map(|s| stmt(s, names)).collect();
    items.into_iter().rev().fold(Stmts::Nil, |rest, s| Stmts::Cons(Box::new(s), Box::new(rest)))
}

// ------------------------------------------------------------------ the contract lexer

/// Cut the text of a contract line into tokens. Any character with no token is `Tok::Unknown`, and the parser refuses the line there.
fn lex(text: &str, line: u32, names: &mut Names) -> Vec<Tok> {
    const OPS: [(&str, BinOp); 12] = [
        ("==>", BinOp::Implies),
        ("&&", BinOp::And),
        ("||", BinOp::Or),
        ("<=", BinOp::Le),
        (">=", BinOp::Ge),
        ("==", BinOp::Eq),
        ("!=", BinOp::Ne),
        ("<", BinOp::Lt),
        (">", BinOp::Gt),
        ("+", BinOp::Add),
        ("-", BinOp::Sub),
        ("*", BinOp::Mul),
    ];
    let mut toks = Vec::new();
    let mut rest = text;
    while let Some(c) = rest.chars().next() {
        let word_end = |pred: fn(char) -> bool| rest.find(|ch: char| !pred(ch)).unwrap_or(rest.len());
        if c.is_whitespace() {
            rest = rest.trim_start();
        } else if c.is_ascii_alphabetic() || c == '_' {
            let end = word_end(|ch| ch.is_ascii_alphanumeric() || ch == '_');
            toks.push(match &rest[..end] {
                "result" => Tok::Result,
                "forall" => Tok::Forall,
                w => Tok::Ident(names.id(w)),
            });
            rest = &rest[end..];
        } else if c.is_ascii_digit() {
            let end = word_end(|ch| ch.is_ascii_digit());
            toks.push(rest[..end].parse().map_or_else(|_| Tok::Unknown(names.id("a number above 18446744073709551615"), line), Tok::Int));
            rest = &rest[end..];
        } else if let Some(t) = [(".size()", Tok::Size), ("::", Tok::ColonColon)].into_iter().find(|(s, _)| rest.starts_with(s)) {
            rest = &rest[t.0.len()..];
            toks.push(t.1);
        } else if c == '.' && rest[1..].starts_with(|ch: char| ch.is_ascii_alphabetic() || ch == '_') {
            let end = 1 + rest[1..].find(|ch: char| !(ch.is_ascii_alphanumeric() || ch == '_')).unwrap_or(rest.len() - 1);
            toks.push(Tok::Field(names.id(&rest[1..end])));
            rest = &rest[end..];
        } else if let Some((s, o)) = OPS.iter().find(|(s, _)| rest.starts_with(s)) {
            toks.push(Tok::Op(*o));
            rest = &rest[s.len()..];
        } else {
            toks.push(match c {
                '!' => Tok::Bang,
                '(' => Tok::LParen,
                ')' => Tok::RParen,
                '[' => Tok::LBracket,
                ']' => Tok::RBracket,
                _ => Tok::Unknown(names.id(&format!("'{c}' in a contract")), line),
            });
            rest = &rest[c.len_utf8()..];
        }
    }
    toks
}

/// The names of the parameters of a declaration, in order. A parameter with no name is `'N` by its place, as in `function`.
fn param_names(v: Vec<String>, names: &mut Names) -> CNames {
    let ids: Vec<u32> = v.into_iter().enumerate().map(|(i, n)| names.id(&if n.is_empty() { format!("'{i}") } else { n })).collect();
    ids.into_iter().rev().fold(CNames::Nil, |rest, n| CNames::Cons(n, Box::new(rest)))
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
        let (kind, e) = if c.text.ends_with('\\') || c.kind.ends_with('\\') {
            (CondKind::Bad(Refusal::Backslash(line)), Expr::Int(0))
        } else {
            match c.kind.as_str() {
                "requires" | "ensures" | "invariant" | "decreases" => {
                    let want = match c.kind.as_str() {
                        "requires" => CondKind::Requires,
                        "ensures" => CondKind::Ensures,
                        "invariant" => CondKind::Invariant,
                        _ => CondKind::Decreases,
                    };
                    match parse_contract(&lex(&c.text, line, names), line) {
                        Ok(e) => (want, e),
                        Err(r) => (CondKind::Bad(r), Expr::Int(0)),
                    }
                }
                word => (CondKind::Other(names.id(word)), Expr::Int(0)),
            }
        };
        items.push((kind, e, line, param_names(c.params, names)));
    }
    items.into_iter().rev().fold(Conds::Nil, |rest, (k, e, l, p)| Conds::Cons(k, e, l, p, Box::new(rest)))
}

// ------------------------------------------------------------------ names that Dafny can read

/// Every name in an expression that the Dafny text will print.
fn expr_names<'a>(e: &'a JExpr, out: &mut Vec<&'a str>) {
    match e {
        JExpr::Var(v, _) => out.push(v),
        JExpr::Bin(_, a, b) | JExpr::Index(a, b) => {
            expr_names(a, out);
            expr_names(b, out);
        }
        JExpr::Not(a) | JExpr::Neg(a) | JExpr::Cast(_, a) | JExpr::Paren(a) | JExpr::Brace(a) | JExpr::Size(a) | JExpr::Copy(a, ..) | JExpr::Field(a, _) => expr_names(a, out),
        JExpr::Call(_, _, args, _) | JExpr::Construct(_, args) => args.iter().for_each(|a| expr_names(a, out)),
        JExpr::Lit(..) | JExpr::Bool(_) | JExpr::Unknown(..) => {}
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
    let mut names = vec![f.name.as_str()];
    names.extend(f.params.iter().map(|(n, _)| n.as_str()));
    f.body.iter().for_each(|s| stmt_names(s, &mut names));
    names.into_iter().find(|n| !n.chars().all(|c| c.is_ascii_alphanumeric() || c == '_'))
}

fn function(f: JFunction, names: &mut Names) -> Function {
    let name = names.id(&f.key);
    names.file = f.file;
    // A parameter with no name is named by its position, as `'N`. C++ cannot write that, so it clashes with no name. The mangling makes it `v_'N`.
    let ps: Vec<(u32, Ty)> = f
        .params
        .into_iter()
        .enumerate()
        .map(|(i, (n, t))| (names.id(&if n.is_empty() { format!("'{i}") } else { n }), ty(t, names)))
        .collect();
    let params = ps.into_iter().rev().fold(Params::Nil, |rest, (n, t)| Params::Cons(n, t, Box::new(rest)));
    let ret = ty(f.ret, names);
    let line = names.here(f.line);
    Function { name, line, params, ret, conds: conds(f.conds, names), body: stmts(f.body, names) }
}

// ------------------------------------------------------------------ the Dafny text

const PRELUDE: &str = "newtype int32 = x: int | -0x8000_0000 <= x < 0x8000_0000\n\
newtype int64 = x: int | -0x8000_0000_0000_0000 <= x < 0x8000_0000_0000_0000\n\
newtype uint8 = x: int | 0 <= x < 0x100\n\
newtype uint32 = x: int | 0 <= x < 0x1_0000_0000\n\
newtype uint64 = x: int | 0 <= x < 0x1_0000_0000_0000_0000\n";

fn dscalar(s: Scalar) -> &'static str {
    match s {
        Scalar::I32 => "int32",
        Scalar::I64 => "int64",
        Scalar::U8 => "uint8",
        Scalar::U32 => "uint32",
        Scalar::U64 => "uint64",
        Scalar::Bool => "bool",
    }
}

fn dty(t: DTy, names: &Names) -> String {
    match t {
        DTy::Int32 => "int32".to_string(),
        DTy::Int64 => "int64".to_string(),
        DTy::UInt8 => "uint8".to_string(),
        DTy::UInt32 => "uint32".to_string(),
        DTy::UInt64 => "uint64".to_string(),
        DTy::Bool => "bool".to_string(),
        DTy::Seq(s) => format!("seq<{}>", dscalar(s)),
        DTy::Struct(k) => names.datatypes[&k].clone(),
    }
}

fn dop(o: BinOp) -> &'static str {
    match o {
        BinOp::Add => "+",
        BinOp::Sub => "-",
        BinOp::Mul => "*",
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
        DExpr::Ctor(k, args) => {
            let mut shown = Vec::new();
            let mut rest = &**args;
            while let DArgs::Cons(a, next) = rest {
                shown.push(dexpr(a, names));
                rest = next;
            }
            format!("{}({})", names.datatypes[k], shown.join(", "))
        }
        DExpr::Len(a) => format!("|{}|", dexpr(a, names)),
        DExpr::Index(a, i) => format!("{}[{}]", dexpr(a, names), dexpr(i, names)),
        // The prefix `b_` keeps a bound name apart from `v_` and `c_` names.
        DExpr::Forall(j, b) => format!("(forall b_{}: int :: {})", names.text(*j), dexpr(b, names)),
        DExpr::Bound(j) => format!("b_{}", names.text(*j)),
        DExpr::Chain(o1, o2, a, b, c) => format!("({} {} {} {} {})", dexpr(a, names), dop(*o1), dexpr(b, names), dop(*o2), dexpr(c, names)),
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
    /// The file and line of each place.
    pub places: Vec<(String, u32)>,
    /// The word and text of the contract line at a place, as the author wrote them.
    pub contracts: HashMap<u32, (String, String)>,
}

pub struct Translation {
    pub dafny: String,
    pub refusals: Vec<Refusing>,
    pub map: Map,
}

/// The printer of the Dafny text. It writes one line at a time, and keeps the map for each line it writes.
struct Printer<'a> {
    names: &'a Names,
    methods: &'a Methods,
    out: String,
    lines: Vec<Option<Line>>,
    /// The contract lines in scope now.
    scope: Vec<u32>,
    /// The invariants of the loop whose invariant and decreases lines are being written.
    own: Vec<u32>,
}

impl Printer<'_> {
    fn put(&mut self, depth: usize, text: String, place: u32) {
        writeln!(self.out, "{}{text}", "  ".repeat(depth)).unwrap();
        self.lines.push(Some(Line { place, scope: self.scope.clone(), own: self.own.clone() }));
    }

    fn call(&self, m: u32, args: &DArgs) -> String {
        let mut shown = Vec::new();
        let mut rest = args;
        while let DArgs::Cons(a, next) = rest {
            shown.push(dexpr(a, self.names));
            rest = next;
        }
        format!("{}({})", self.methods[&m], shown.join(", "))
    }

    fn stmts(&mut self, ss: &DStmts, depth: usize) {
        let mut rest = ss;
        while let DStmts::Cons(s, place, next) = rest {
            self.stmt(s, *place, depth);
            rest = next;
        }
    }

    /// A `while`: the condition, the invariants, the decreases lines, then the body. A `for` has its step as the last statement of the body.
    /// The `while` line and the body have the invariants of the loop in scope. The invariant and decreases lines have them as `own`.
    fn dwhile(&mut self, (c, place): (&DExpr, u32), lists: [&DConds; 2], body: &DStmts, step: Option<(&DStmt, u32)>, depth: usize) {
        let mut invariants = Vec::new();
        let mut cs = lists[0];
        while let DConds::Cons(_, line, next) = cs {
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
            while let DConds::Cons(e, line, next) = cs {
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
            DStmt::Return(e) => self.put(depth, format!("return {};", dexpr(e, names)), place),
            DStmt::Local(x, t, e) => self.put(depth, format!("var {}: {} := {};", mangle(names.text(*x)), dty(*t, names), dexpr(e, names)), place),
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
                if matches!(**f, DStmts::Nil) {
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
    fn header(&mut self, name: u32, params: &DParams, ret: DTy, place: u32) {
        let mut shown = Vec::new();
        let mut ps = params;
        while let DParams::Cons(n, t, next) = ps {
            shown.push(format!("{}: {}", mangle(self.names.text(*n)), dty(*t, self.names)));
            ps = next;
        }
        self.out.push('\n');
        self.lines.push(None);
        self.put(0, format!("method {}({}) returns (result: {})", self.methods[&name], shown.join(", "), dty(ret, self.names)), place);
    }

    fn method(&mut self, m: &Method, place: u32) {
        self.header(m.name, &m.params, m.ret, place);
        // A requires line has the requires lines before it in scope, and an ensures or decreases line and the body have all of them.
        for (word, list) in [("requires", &m.requires), ("ensures", &m.ensures), ("decreases", &m.decreases)] {
            let mut cs = list;
            while let DConds::Cons(e, line, next) = cs {
                self.put(1, format!("{word} {}", dexpr(e, self.names)), *line);
                if word == "requires" {
                    self.scope.push(*line);
                }
                cs = next;
            }
        }
        self.put(0, "{".to_string(), place);
        self.stmts(&m.body, 1);
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
        Refusal::Syntax(line) => (line, "the contract line has a form the translator cannot read.".to_string()),
        Refusal::Backslash(line) => (line, "a contract line that ends in a backslash.".to_string()),
        Refusal::Callee(n, line) => (line, format!("a call to {}, which has no model in view.", names.text(n))),
        Refusal::Place(line) => {
            (line, "a call inside an expression. The translator takes a call only as the full value of a return or of a local.".to_string())
        }
        Refusal::Twice(n, line) => (line, format!("{} is declared twice in the function.", names.text(n))),
        Refusal::Convert(line) => (line, "a conversion between bool and a number.".to_string()),
        Refusal::WriteParam(n, line) => (line, format!("{} is a parameter. The translator writes only a local.", names.text(n))),
        Refusal::NoVar(n, line) => (line, format!("{} in the loop contract is no variable.", names.text(n))),
        Refusal::SeqParam(line) => (line, "a sequence is in the subset only as a parameter.".to_string()),
        Refusal::Extent(line) => (line, "a sequence made from one of another length or element.".to_string()),
        Refusal::Misplaced(line) => (
            line,
            "a contract line in the wrong place. A requires, an ensures or a decreases line goes above a function. An invariant or a decreases line goes above a loop."
                .to_string(),
        ),
    }
}

/// A refusal: the file, the line and the sentence.
pub type Refusing = (String, u32, String);

/// The Dafny file for the plugin's lines, the refusals in order each once, and the map from the lines of the file to C++. A function whose
/// signature is refused is not in the file. A function whose contract or body is refused is a method with no contract and no body. A `//@`
/// line that no function claimed is a refusal too.
pub fn translate(lines: &str) -> Result<Translation> {
    let mut names = Names::default();
    let mut refusals = Vec::new();
    let mut funcs = Vec::new();
    let mut structs = Vec::new();
    for l in lines.lines().filter(|l| !l.trim().is_empty()) {
        match serde_json::from_str(l).with_context(|| format!("cannot read a line of the tree: {l}"))? {
            Item::Orphan { orphan, file } => refusals.push((file, orphan, "a contract line that belongs to no function.".to_string())),
            Item::Struct(st) => structs.push(st),
            Item::Function(f) => match unreadable_name(&f) {
                Some(n) => refusals.push((f.file.clone(), f.line, format!("{n}: a name with a character Dafny cannot read."))),
                None => funcs.push(f),
            },
        }
    }
    // The Dafny names, by key.
    // ponytail: a count of each plain name for each function. A file has dozens of functions. Upgrade: one pass with a map.
    let mut methods = Methods::new();
    // The place of each function, by the id of its key, for its method header.
    let mut at = HashMap::new();
    for (i, f) in funcs.iter().enumerate() {
        let same = funcs.iter().filter(|g| g.name == f.name).count();
        let k = funcs[..=i].iter().filter(|g| g.name == f.name).count();
        let dafny = if same == 1 { format!("c_{}", f.name) } else { format!("c_{}'{k}", f.name) };
        let key = names.id(&f.key);
        methods.insert(key, dafny);
        at.insert(key, names.place(&f.file, f.line));
    }
    // The Dafny name of each struct: `S_{plain}`, or `S_{plain}'{k}` when two structs share a plain name.
    let mut table = Structs::Nil;
    for (i, st) in structs.iter().enumerate() {
        let same = structs.iter().filter(|g| g.name == st.name).count();
        let k = structs[..=i].iter().filter(|g| g.name == st.name).count();
        let key = names.id(&st.key);
        names.datatypes.insert(key, if same == 1 { format!("S_{}", st.name) } else { format!("S_{}'{k}", st.name) });
    }
    let struct_places: Vec<u32> = structs.iter().map(|st| names.place(&st.file, st.line)).collect();
    for st in structs.into_iter().rev() {
        let key = names.id(&st.key);
        let place = names.place(&st.file, st.line);
        names.file = st.file;
        let fields = st.fields.into_iter().rev().fold(Params::Nil, |rest, (n, t)| Params::Cons(names.id(&n), ty(t, &mut names), Box::new(rest)));
        table = Structs::Cons(key, place, fields, Box::new(table));
    }
    let count = funcs.len();
    let fns = funcs.into_iter().rev().map(|f| function(f, &mut names)).fold(Fns::Nil, |rest, f| Fns::Cons(Box::new(f), Box::new(rest)));
    let mut models = translate_unit(&fns, &table);
    let mut smodels = translate_structs(&table);
    let mut p = Printer { names: &names, methods: &methods, out: PRELUDE.to_string(), lines: Vec::new(), scope: Vec::new(), own: Vec::new() };
    p.lines.extend(PRELUDE.lines().map(|_| None));
    let mut refused_at = Vec::new();
    for place in struct_places {
        let StructModels::Cons(model, rest) = smodels else { unreachable!("one model for each struct") };
        match model {
            Ok((key, DParams::Nil)) => p.put(0, format!("datatype {0} = {0}()", names.datatypes[&key]), place),
            Ok((key, mut fields)) => {
                let mut shown = Vec::new();
                while let DParams::Cons(n, t, next) = fields {
                    shown.push(format!("f_{}: {}", names.text(n), dty(t, &names)));
                    fields = *next;
                }
                p.put(0, format!("datatype {0} = {0}({1})", names.datatypes[&key], shown.join(", ")), place);
            }
            Err(r) => refused_at.push(sentence(r, &names)),
        }
        smodels = *rest;
    }
    for _ in 0..count {
        let Models::Cons(model, rest) = models else { unreachable!("one model for each function") };
        let refused = match model {
            Model::Full(m) => {
                p.method(&m, at[&m.name]);
                None
            }
            Model::Bare(key, params, ret, r) => {
                p.header(key, &params, ret, at[&key]);
                Some(r)
            }
            Model::Refused(r) => Some(r),
        };
        refused_at.extend(refused.map(|r| sentence(r, &names)));
        models = *rest;
    }
    let (dafny, lines) = (p.out, p.lines);
    for (place, sentence) in refused_at {
        let (file, line) = names.places[place as usize].clone();
        refusals.push((file, line, sentence));
    }
    refusals.sort();
    refusals.dedup();
    Ok(Translation { dafny, refusals, map: Map { lines, places: names.places, contracts: names.contracts } })
}
