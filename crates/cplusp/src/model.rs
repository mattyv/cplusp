//! The shell side of the translator, decisions 0056 and 0057. It reads the plugin's lines of JSON, numbers the names, cuts the contract
//! lines into tokens, hands the core its types, and prints the Dafny text of what the core gives back. Every rule of the translation is
//! in `cplusp_core::model`. Nothing here decides what is allowed.

use std::fmt::Write;

use anyhow::{Context, Result};
use cplusp_core::model::{
    parse_contract, translate_function, BinOp, CastKind, CondKind, Conds, DConds, DExpr, DParams, DStmt, DStmts, DTy, Expr, Function, Method,
    Params, Refusal, Stmt, Stmts, Tok, Ty,
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
    Other(String),
}

#[derive(Deserialize)]
enum JExpr {
    Int(i64),
    Var(String, JTy),
    Bin(JOp, Box<JExpr>, Box<JExpr>),
    Not(Box<JExpr>),
    Neg(Box<JExpr>),
    Cast(JCast, Box<JExpr>),
    Paren(Box<JExpr>),
    Unknown(String, u32),
}

#[derive(Deserialize)]
enum JStmt {
    Return(JExpr),
    If(JExpr, Vec<JStmt>, Vec<JStmt>),
    Unknown(String, u32),
}

#[derive(Deserialize)]
struct JCond {
    kind: String,
    line: u32,
    text: String,
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
        JExpr::Int(n) => Expr::Int(n),
        JExpr::Var(v, t) => Expr::Var(names.id(&v), ty(t, names)),
        JExpr::Bin(o, a, b) => Expr::Bin(op(o), Box::new(expr(*a, names)), Box::new(expr(*b, names))),
        JExpr::Not(a) => Expr::Not(Box::new(expr(*a, names))),
        JExpr::Neg(a) => Expr::Neg(Box::new(expr(*a, names))),
        JExpr::Cast(k, a) => {
            let kind = match k {
                JCast::Read => CastKind::Read,
                JCast::NoOp => CastKind::NoOp,
                JCast::Other(s) => CastKind::Other(names.id(&s)),
            };
            Expr::Cast(kind, Box::new(expr(*a, names)))
        }
        JExpr::Paren(a) => Expr::Paren(Box::new(expr(*a, names))),
        JExpr::Unknown(k, line) => Expr::Unknown(names.id(&k), line),
    }
}

fn stmt(s: JStmt, names: &mut Names) -> Stmt {
    match s {
        JStmt::Return(e) => Stmt::Return(expr(e, names)),
        JStmt::If(c, t, f) => Stmt::If(expr(c, names), Box::new(stmts(t, names)), Box::new(stmts(f, names))),
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

/// The contract lines as the core's list. A word other than `requires` and `ensures` has no grammar yet, so its text is not parsed.
/// The core refuses the line by its word.
fn conds(v: Vec<JCond>, names: &mut Names) -> Result<Conds, Refused> {
    let mut items = Vec::new();
    for c in v {
        // A backslash at the end splices the next line into the comment. The line the author wrote is not the one the plugin read.
        if c.text.ends_with('\\') || c.kind.ends_with('\\') {
            return Err(Refused::Backslash(c.line));
        }
        let (kind, e) = match c.kind.as_str() {
            "requires" => (CondKind::Requires, parse_contract(&lex(&c.text, c.line, names), c.line)?),
            "ensures" => (CondKind::Ensures, parse_contract(&lex(&c.text, c.line, names), c.line)?),
            word => (CondKind::Other(names.id(word)), Expr::Int(0)),
        };
        items.push((kind, e, c.line));
    }
    Ok(items.into_iter().rev().fold(Conds::Nil, |rest, (k, e, l)| Conds::Cons(k, e, l, Box::new(rest))))
}

/// Why a function is refused before or by the core. `Backslash` is the shell's own: a contract line that ends in a backslash.
enum Refused {
    Core(Refusal),
    Backslash(u32),
}

impl From<Refusal> for Refused {
    fn from(r: Refusal) -> Self {
        Refused::Core(r)
    }
}

fn function(f: JFunction, names: &mut Names) -> Result<Function, Refused> {
    let name = names.id(&f.name);
    // A parameter with no name is named by its position. The mangling makes it `c__N`.
    let ps: Vec<(u32, Ty)> = f
        .params
        .into_iter()
        .enumerate()
        .map(|(i, (n, t))| (names.id(&if n.is_empty() { format!("_{i}") } else { n }), ty(t, names)))
        .collect();
    let params = ps.into_iter().rev().fold(Params::Nil, |rest, (n, t)| Params::Cons(n, t, Box::new(rest)));
    let ret = ty(f.ret, names);
    // ponytail: a contract line that does not parse refuses the function before the core sees it. The core has no way to carry a
    // refusal of the parser inside `Conds`, so a bad line wins over a bad body. The bot sees one refusal per function per run, so it
    // fixes the line first, and the body on the next run. Upgrade: a `Bad` kind of line in `Conds`.
    let conds = conds(f.conds, names)?;
    Ok(Function { name, line: f.line, params, ret, conds, body: stmts(f.body, names) })
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

/// The one mangling of a C++ name for Dafny, for code and contract alike. The prefix keeps a name clear of the words Dafny reserves,
/// such as `old` and `function`, and of `result`. The contract word `result` is no name: it is `Tok::Result`, and prints as `result`.
// ponytail: an unnamed parameter is `c__N`, so a parameter that the author calls `_N` has the same name, and Dafny refuses the method.
// Upgrade: a prefix that C++ cannot write.
fn mangle(name: &str) -> String {
    format!("c_{name}")
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
    }
}

fn dstmts(ss: &DStmts, names: &Names, depth: usize, out: &mut String) {
    let pad = "  ".repeat(depth);
    let mut rest = ss;
    while let DStmts::Cons(s, next) = rest {
        match &**s {
            DStmt::Return(e) => writeln!(out, "{pad}return {};", dexpr(e, names)).unwrap(),
            DStmt::If(c, t, f) => {
                writeln!(out, "{pad}if {} {{", dexpr(c, names)).unwrap();
                dstmts(t, names, depth + 1, out);
                if matches!(**f, DStmts::Nil) {
                    writeln!(out, "{pad}}}").unwrap();
                } else {
                    writeln!(out, "{pad}}} else {{").unwrap();
                    dstmts(f, names, depth + 1, out);
                    writeln!(out, "{pad}}}").unwrap();
                }
            }
        }
        rest = next;
    }
}

fn dmethod(m: &Method, names: &Names) -> String {
    let mut params = Vec::new();
    let mut ps = &m.params;
    while let DParams::Cons(n, t, next) = ps {
        params.push(format!("{}: {}", mangle(names.text(*n)), dty(*t)));
        ps = next;
    }
    let mut out = format!("\nmethod {}({}) returns (result: {})\n", mangle(names.text(m.name)), params.join(", "), dty(m.ret));
    for (word, list) in [("requires", &m.requires), ("ensures", &m.ensures)] {
        let mut cs = list;
        while let DConds::Cons(e, next) = cs {
            writeln!(out, "  {word} {}", dexpr(e, names)).unwrap();
            cs = next;
        }
    }
    out.push_str("{\n");
    dstmts(&m.body, names, 1, &mut out);
    out.push_str("}\n");
    out
}

/// A refusal as the line it points at and the sentence the bot reads.
fn sentence(r: Refused, names: &Names) -> (u32, String) {
    match r {
        Refused::Core(Refusal::Construct(k, line)) => (line, format!("{}: the translator has no rule for it yet.", names.text(k))),
        Refused::Core(Refusal::Name(n, line)) => (line, format!("{} in the contract is no parameter.", names.text(n))),
        Refused::Core(Refusal::Syntax(line)) => (line, "the contract line has a form the translator cannot read.".to_string()),
        Refused::Backslash(line) => (line, "a contract line that ends in a backslash.".to_string()),
    }
}

/// A refusal: the file, the line and the sentence.
pub type Refusing = (String, u32, String);

/// The Dafny file for the plugin's lines, and the refusals in order, each once. A refused function is not in the file. A `//@` line
/// that no function claimed is a refusal too.
pub fn translate(lines: &str) -> Result<(String, Vec<Refusing>)> {
    let mut names = Names::default();
    let mut dafny = PRELUDE.to_string();
    let mut refusals = Vec::new();
    for l in lines.lines().filter(|l| !l.trim().is_empty()) {
        match serde_json::from_str(l).with_context(|| format!("cannot read a line of the tree: {l}"))? {
            Item::Orphan { orphan, file } => refusals.push((file, orphan, "a contract line that belongs to no function.".to_string())),
            Item::Function(f) => {
                let file = f.file.clone();
                match function(f, &mut names).and_then(|f| translate_function(&f).map_err(Refused::Core)) {
                    Ok(m) => dafny += &dmethod(&m, &names),
                    Err(r) => {
                        let (line, sentence) = sentence(r, &names);
                        refusals.push((file, line, sentence));
                    }
                }
            }
        }
    }
    refusals.sort();
    refusals.dedup();
    Ok((dafny, refusals))
}
