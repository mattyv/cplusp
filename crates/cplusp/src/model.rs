//! The shell side of the translator, decisions 0056 and 0057. It reads the plugin's lines of JSON, numbers the names, cuts the contract
//! lines into tokens, hands the core its types, and prints the Dafny text of what the core gives back. Every rule of the translation is
//! in `cplusp_core::model`. Nothing here decides what is allowed.

use std::collections::HashMap;
use std::fmt::Write;

use anyhow::{Context, Result};
use cplusp_core::model::{
    parse_contract, translate_unit, Args, BinOp, CastKind, CondKind, Conds, DArgs, DConds, DExpr, DParams, DStmt, DStmts, DTy, Expr, Fns,
    Function, Method, Model, Models, Names as CNames, Params, Refusal, Stmt, Stmts, Tok, Ty,
};
use serde::Deserialize;

// ------------------------------------------------------------------ the plugin's lines, in the core's shape with names as text

#[derive(Deserialize)]
enum JTy {
    I32,
    I64,
    U8,
    Bool,
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
    Integral(JTy, JTy),
    Other(String),
}

#[derive(Deserialize)]
enum JExpr {
    Lit(i64, JTy),
    Var(String, JTy),
    Bin(JOp, Box<JExpr>, Box<JExpr>),
    Not(Box<JExpr>),
    Neg(Box<JExpr>),
    Cast(JCast, Box<JExpr>),
    Paren(Box<JExpr>),
    Brace(Box<JExpr>),
    Call(String, String, Vec<JExpr>, u32),
    Unknown(String, u32),
}

#[derive(Deserialize)]
enum JStmt {
    Return(JExpr, u32),
    If(JExpr, Vec<JStmt>, Vec<JStmt>, u32),
    Local(String, JTy, JExpr, u32),
    Unknown(String, u32),
}

#[derive(Deserialize)]
struct JCond {
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
    Function(JFunction),
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
// ponytail: a linear search. A file has dozens of names. Upgrade: a hash map.
#[derive(Default)]
struct Names(Vec<String>);

impl Names {
    fn id(&mut self, s: &str) -> u32 {
        let at = self.0.iter().position(|n| n == s).unwrap_or_else(|| {
            self.0.push(s.to_string());
            self.0.len() - 1
        });
        at as u32
    }
    fn text(&self, id: u32) -> &str {
        &self.0[id as usize]
    }
}

// ------------------------------------------------------------------ from JSON to the core's types

fn ty(t: JTy, names: &mut Names) -> Ty {
    match t {
        JTy::I32 => Ty::I32,
        JTy::I64 => Ty::I64,
        JTy::U8 => Ty::U8,
        JTy::Bool => Ty::Bool,
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
        JExpr::Var(v, t) => Expr::Var(names.id(&v), ty(t, names)),
        JExpr::Bin(o, a, b) => Expr::Bin(op(o), Box::new(expr(*a, names)), Box::new(expr(*b, names))),
        JExpr::Not(a) => Expr::Not(Box::new(expr(*a, names))),
        JExpr::Neg(a) => Expr::Neg(Box::new(expr(*a, names))),
        JExpr::Cast(k, a) => {
            let kind = match k {
                JCast::Read => CastKind::Read,
                JCast::NoOp => CastKind::NoOp,
                JCast::Integral(from, to) => CastKind::Integral(ty(from, names), ty(to, names)),
                JCast::Other(s) => CastKind::Other(names.id(&s)),
            };
            Expr::Cast(kind, Box::new(expr(*a, names)))
        }
        JExpr::Paren(a) => Expr::Paren(Box::new(expr(*a, names))),
        JExpr::Brace(a) => Expr::Brace(Box::new(expr(*a, names))),
        JExpr::Call(key, name, args, line) => {
            let args: Vec<Expr> = args.into_iter().map(|a| expr(a, names)).collect();
            let args = args.into_iter().rev().fold(Args::Nil, |rest, a| Args::Cons(Box::new(a), Box::new(rest)));
            Expr::Call(names.id(&key), names.id(&name), Box::new(args), line)
        }
        JExpr::Unknown(k, line) => Expr::Unknown(names.id(&k), line),
    }
}

fn stmt(s: JStmt, names: &mut Names) -> Stmt {
    match s {
        JStmt::Return(e, line) => Stmt::Return(expr(e, names), line),
        JStmt::If(c, t, f, line) => Stmt::If(expr(c, names), Box::new(stmts(t, names)), Box::new(stmts(f, names)), line),
        JStmt::Local(n, t, e, line) => Stmt::Local(names.id(&n), ty(t, names), expr(e, names), line),
        JStmt::Unknown(k, line) => Stmt::Unknown(names.id(&k), line),
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
            toks.push(if &rest[..end] == "result" { Tok::Result } else { Tok::Ident(names.id(&rest[..end])) });
            rest = &rest[end..];
        } else if c.is_ascii_digit() {
            let end = word_end(|ch| ch.is_ascii_digit());
            toks.push(rest[..end].parse().map_or_else(|_| Tok::Unknown(names.id("a number above 9223372036854775807"), line), Tok::Int));
            rest = &rest[end..];
        } else if let Some((s, o)) = OPS.iter().find(|(s, _)| rest.starts_with(s)) {
            toks.push(Tok::Op(*o));
            rest = &rest[s.len()..];
        } else {
            toks.push(match c {
                '!' => Tok::Bang,
                '(' => Tok::LParen,
                ')' => Tok::RParen,
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

/// The contract lines as the core's list. A word other than `requires` and `ensures` has no grammar yet, so its text is not parsed.
/// The core refuses the line by its word. A line that the parser refuses, or that ends in a backslash, is `Bad`, and the core refuses it
/// with that refusal.
fn conds(v: Vec<JCond>, names: &mut Names) -> Conds {
    let mut items = Vec::new();
    for c in v {
        // A backslash at the end splices the next line into the comment. The line the author wrote is not the one the plugin read.
        let (kind, e) = if c.text.ends_with('\\') || c.kind.ends_with('\\') {
            (CondKind::Bad(Refusal::Backslash(c.line)), Expr::Int(0))
        } else {
            match c.kind.as_str() {
                "requires" | "ensures" => {
                    let want = if c.kind == "requires" { CondKind::Requires } else { CondKind::Ensures };
                    match parse_contract(&lex(&c.text, c.line, names), c.line) {
                        Ok(e) => (want, e),
                        Err(r) => (CondKind::Bad(r), Expr::Int(0)),
                    }
                }
                word => (CondKind::Other(names.id(word)), Expr::Int(0)),
            }
        };
        items.push((kind, e, c.line, param_names(c.params, names)));
    }
    items.into_iter().rev().fold(Conds::Nil, |rest, (k, e, l, p)| Conds::Cons(k, e, l, p, Box::new(rest)))
}

fn function(f: JFunction, names: &mut Names) -> Function {
    let name = names.id(&f.key);
    // A parameter with no name is named by its position, as `'N`. C++ cannot write that, so it clashes with no name. The mangling makes it `v_'N`.
    let ps: Vec<(u32, Ty)> = f
        .params
        .into_iter()
        .enumerate()
        .map(|(i, (n, t))| (names.id(&if n.is_empty() { format!("'{i}") } else { n }), ty(t, names)))
        .collect();
    let params = ps.into_iter().rev().fold(Params::Nil, |rest, (n, t)| Params::Cons(n, t, Box::new(rest)));
    let ret = ty(f.ret, names);
    Function { name, line: f.line, params, ret, conds: conds(f.conds, names), body: stmts(f.body, names) }
}

// ------------------------------------------------------------------ the Dafny text

const PRELUDE: &str = "newtype int32 = x: int | -0x8000_0000 <= x < 0x8000_0000\n\
newtype int64 = x: int | -0x8000_0000_0000_0000 <= x < 0x8000_0000_0000_0000\n\
newtype uint8 = x: int | 0 <= x < 0x100\n";

fn dty(t: DTy) -> &'static str {
    match t {
        DTy::Int32 => "int32",
        DTy::Int64 => "int64",
        DTy::UInt8 => "uint8",
        DTy::Bool => "bool",
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
        DExpr::Var(v) => mangle(names.text(*v)),
        DExpr::Result => "result".to_string(),
        DExpr::Bin(o, a, b) => format!("({} {} {})", dexpr(a, names), dop(*o), dexpr(b, names)),
        DExpr::Not(a) => format!("(!{})", dexpr(a, names)),
        DExpr::Neg(a) => format!("(-{})", dexpr(a, names)),
        DExpr::AsInt(a) => format!("({} as int)", dexpr(a, names)),
        DExpr::Conv(t, a) => format!("({} as {})", dexpr(a, names), dty(*t)),
    }
}

/// The Dafny name of each function by the id of its key, with the method prefix `c_`. `c_{plain}` when the plain name is unique among the file's functions, else
/// `c_{plain}'{k}`, with k counting the functions of that plain name in file order from 1.
type Methods = HashMap<u32, String>;

fn call(m: u32, args: &DArgs, names: &Names, methods: &Methods) -> String {
    let mut shown = Vec::new();
    let mut rest = args;
    while let DArgs::Cons(a, next) = rest {
        shown.push(dexpr(a, names));
        rest = next;
    }
    format!("{}({})", methods[&m], shown.join(", "))
}

fn dstmts(ss: &DStmts, names: &Names, methods: &Methods, depth: usize, out: &mut String) {
    let pad = "  ".repeat(depth);
    let mut rest = ss;
    while let DStmts::Cons(s, next) = rest {
        match &**s {
            DStmt::Return(e) => writeln!(out, "{pad}return {};", dexpr(e, names)).unwrap(),
            DStmt::Local(x, t, e) => writeln!(out, "{pad}var {}: {} := {};", mangle(names.text(*x)), dty(*t), dexpr(e, names)).unwrap(),
            DStmt::LocalCall(x, t, m, args) => {
                writeln!(out, "{pad}var {}: {} := {};", mangle(names.text(*x)), dty(*t), call(*m, args, names, methods)).unwrap()
            }
            DStmt::ReturnCall(m, args) => {
                writeln!(out, "{pad}result := {};", call(*m, args, names, methods)).unwrap();
                writeln!(out, "{pad}return;").unwrap();
            }
            DStmt::If(c, t, f) => {
                writeln!(out, "{pad}if {} {{", dexpr(c, names)).unwrap();
                dstmts(t, names, methods, depth + 1, out);
                if matches!(**f, DStmts::Nil) {
                    writeln!(out, "{pad}}}").unwrap();
                } else {
                    writeln!(out, "{pad}}} else {{").unwrap();
                    dstmts(f, names, methods, depth + 1, out);
                    writeln!(out, "{pad}}}").unwrap();
                }
            }
        }
        rest = next;
    }
}

/// The method header line, with no contract and no body.
fn dheader(name: u32, params: &DParams, ret: DTy, names: &Names, methods: &Methods) -> String {
    let mut shown = Vec::new();
    let mut ps = params;
    while let DParams::Cons(n, t, next) = ps {
        shown.push(format!("{}: {}", mangle(names.text(*n)), dty(*t)));
        ps = next;
    }
    format!("\nmethod {}({}) returns (result: {})\n", methods[&name], shown.join(", "), dty(ret))
}

fn dmethod(m: &Method, names: &Names, methods: &Methods) -> String {
    let mut out = dheader(m.name, &m.params, m.ret, names, methods);
    for (word, list) in [("requires", &m.requires), ("ensures", &m.ensures)] {
        let mut cs = list;
        while let DConds::Cons(e, next) = cs {
            writeln!(out, "  {word} {}", dexpr(e, names)).unwrap();
            cs = next;
        }
    }
    out.push_str("{\n");
    dstmts(&m.body, names, methods, 1, &mut out);
    out.push_str("}\n");
    out
}

/// A refusal as the line it points at and the sentence the bot reads.
fn sentence(r: Refusal, names: &Names) -> (u32, String) {
    match r {
        Refusal::Construct(k, line) => (line, format!("{}: the translator has no rule for it yet.", names.text(k))),
        Refusal::Name(n, line) => (line, format!("{} in the contract is no parameter.", names.text(n))),
        Refusal::Syntax(line) => (line, "the contract line has a form the translator cannot read.".to_string()),
        Refusal::Backslash(line) => (line, "a contract line that ends in a backslash.".to_string()),
        Refusal::Callee(n, line) => (line, format!("a call to {}, which has no model in view.", names.text(n))),
        Refusal::Place(line) => {
            (line, "a call inside an expression. The translator takes a call only as the full value of a return or of a local.".to_string())
        }
        Refusal::Twice(n, line) => (line, format!("{} is declared twice in the function.", names.text(n))),
        Refusal::Convert(line) => (line, "a conversion between bool and a number.".to_string()),
    }
}

/// A refusal: the file, the line and the sentence.
pub type Refusing = (String, u32, String);

/// The Dafny file for the plugin's lines, and the refusals in order, each once. A function whose signature is refused is not in the file.
/// A function whose contract or body is refused is a method with no contract and no body. A `//@` line that no function claimed is a
/// refusal too.
pub fn translate(lines: &str) -> Result<(String, Vec<Refusing>)> {
    let mut names = Names::default();
    let mut refusals = Vec::new();
    let mut funcs = Vec::new();
    for l in lines.lines().filter(|l| !l.trim().is_empty()) {
        match serde_json::from_str(l).with_context(|| format!("cannot read a line of the tree: {l}"))? {
            Item::Orphan { orphan, file } => refusals.push((file, orphan, "a contract line that belongs to no function.".to_string())),
            Item::Function(f) => funcs.push(f),
        }
    }
    // The Dafny names, by key.
    // ponytail: a count of each plain name for each function. A file has dozens of functions. Upgrade: one pass with a map.
    let mut methods = Methods::new();
    for (i, f) in funcs.iter().enumerate() {
        let same = funcs.iter().filter(|g| g.name == f.name).count();
        let k = funcs[..=i].iter().filter(|g| g.name == f.name).count();
        let dafny = if same == 1 { format!("c_{}", f.name) } else { format!("c_{}'{k}", f.name) };
        methods.insert(names.id(&f.key), dafny);
    }
    let files: Vec<String> = funcs.iter().map(|f| f.file.clone()).collect();
    let fns = funcs.into_iter().rev().map(|f| function(f, &mut names)).fold(Fns::Nil, |rest, f| Fns::Cons(Box::new(f), Box::new(rest)));
    let mut dafny = PRELUDE.to_string();
    let mut models = translate_unit(&fns);
    for file in files {
        let Models::Cons(model, rest) = models else { unreachable!("one model for each function") };
        let refused = match model {
            Model::Full(m) => {
                dafny += &dmethod(&m, &names, &methods);
                None
            }
            Model::Bare(key, params, ret, r) => {
                dafny += &dheader(key, &params, ret, &names, &methods);
                Some(r)
            }
            Model::Refused(r) => Some(r),
        };
        if let Some(r) = refused {
            let (line, sentence) = sentence(r, &names);
            refusals.push((file, line, sentence));
        }
        models = *rest;
    }
    refusals.sort();
    refusals.dedup();
    Ok((dafny, refusals))
}
