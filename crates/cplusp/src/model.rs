//! The shell side of the translator, decisions 0056 and 0057. It reads the plugin's lines of JSON, numbers the names, cuts the contract
//! lines into tokens, hands the core its types, and prints the Dafny text of what the core gives back. Every rule of the translation is
//! in `cplusp_core::model`. Nothing here decides what is allowed.

use std::collections::HashMap;
use std::fmt::Write;

use anyhow::{Context, Result};
use cplusp_core::model::{
    parse_contract, translate_structs, translate_unit, Args, BinOp, CastKind, CondKind, Conds, DArgs, DCalls, DConds, DExpr, DParams, DStmt, DStmts, DTy, Expr, Extent, Fns,
    Function, Members, Method, Model, Models, Names as CNames, Obj, Params, Refusal, Scalar, Stmt, Stmts, StructModels, Structs, Tok, Ty,
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
    I32,
    I64,
    U8,
    U32,
    U64,
    Bool,
    Seq(JScalar, Option<u64>),
    Struct(String),
    Opt(JScalar),
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
    Call(String, String, Vec<JExpr>, u32),
    Exit(u32),
    /// A `//@ assert` or `//@ apply` line in the body, decision 0099.
    Assert(JCond),
    Apply(JCond),
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
    Orphan {
        orphan: u32,
        file: String,
        /// The word of the line, when it starts with `//@`.
        #[serde(default)]
        word: String,
    },
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
        JTy::Bool => Ty::Bool,
        JTy::Seq(s, extent) => Ty::Seq(scalar(s, names), extent.map_or(Extent::Dynamic, Extent::Fixed)),
        JTy::Opt(s) => Ty::Opt(scalar(s, names)),
        JTy::Struct(k) => Ty::Struct(names.id(&k)),
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
        JExpr::Var(v, t) => Expr::Var(names.id(&v), ty(t, names)),
        JExpr::Bin(o, a, b) => Expr::Bin(op(o), Box::new(expr(*a, names)), Box::new(expr(*b, names))),
        JExpr::Divide(o, a, b, t) => Expr::Divide(op(o), Box::new(expr(*a, names)), Box::new(expr(*b, names)), ty(t, names)),
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
    toks.extend(lex(text, line, names));
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
    items.into_iter().rev().fold(Stmts::Nil, |rest, s| Stmts::Cons(Box::new(s), Box::new(rest)))
}

// ------------------------------------------------------------------ the contract lexer

/// Cut the text of a contract line into tokens. Any character with no token is `Tok::Unknown`, and the parser refuses the line there.
fn lex(text: &str, line: u32, names: &mut Names) -> Vec<Tok> {
    const OPS: [(&str, BinOp); 14] = [
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
        ("/", BinOp::Div),
        ("%", BinOp::Rem),
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
                // `old(e)` is the word `old` and a parenthesis. A parameter named `old` is a name, decision 0057.
                "old" if rest[end..].trim_start().starts_with('(') => Tok::Old,
                "forall" => Tok::Forall,
                "exists" => Tok::Exists,
                "true" => Tok::Bool(true),
                "false" => Tok::Bool(false),
                w => {
                    // A name followed by `(` is a call, and the companion file must declare it. A member name in a member function may be a call of
                    // the member, and the core decides, decision 0090.
                    if rest[end..].trim_start().starts_with('(') && !names.declared.iter().any(|d| d == w) && !names.this_members.iter().any(|d| d == w) && !names.functors.iter().any(|d| d == w) {
                        names.bad_calls.entry(line).or_insert_with(|| w.to_string());
                    }
                    Tok::Ident(names.id(w))
                }
            });
            rest = &rest[end..];
        } else if c.is_ascii_digit() {
            // A C++ integer, decision 0082: decimal or hex, digit separators `'`, and a suffix of u and l. The value is exact. A literal that cannot be read
            // or does not fit u64 is `Tok::Unknown`, never a token of the grammar.
            let bytes = rest.as_bytes();
            let mut end = 0;
            while end < bytes.len() && (bytes[end].is_ascii_alphanumeric() || (bytes[end] == b'\'' && bytes.get(end + 1).is_some_and(u8::is_ascii_alphanumeric))) {
                end += 1;
            }
            let word: String = rest[..end].chars().filter(|&ch| ch != '\'').collect();
            let (prefix, digits, radix) = match word.strip_prefix("0x").or_else(|| word.strip_prefix("0X")) {
                Some(h) => (&word[..2], h, 16),
                None => ("", word.as_str(), 10),
            };
            let n = &digits[..digits.find(|ch: char| !ch.is_digit(radix)).unwrap_or(digits.len())];
            let suffix = &digits[n.len()..];
            let bad_suffix = !["", "u", "l", "ul", "lu", "ll", "ull", "llu"].contains(&suffix.to_ascii_lowercase().as_str());
            // A leading 0 with more digits is octal in C++, and its digits say another number.
            let refused = if n.is_empty() {
                Some(format!("a number with no digits after {prefix}"))
            } else if radix == 10 && n.len() > 1 && n.starts_with('0') {
                Some("an octal number".to_string())
            } else if bad_suffix {
                Some(format!("a number with the suffix {suffix}"))
            } else {
                None
            };
            let value = match refused {
                Some(kind) => Err(kind),
                None => u64::from_str_radix(n, radix).map_err(|_| "a number above 18446744073709551615".to_string()),
            };
            toks.push(value.map_or_else(|kind| Tok::Unknown(names.id(&kind), line), Tok::Int));
            rest = &rest[end..];
        } else if let Some(t) = [(".size()", Tok::Size), (".empty()", Tok::Empty), (".has_value()", Tok::HasValue), (".value()", Tok::Value), ("..", Tok::DotDot), ("::", Tok::ColonColon)].into_iter().find(|(s, _)| rest.starts_with(s)) {
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
                ',' => Tok::Comma,
                '?' => Tok::Question,
                ':' => Tok::Colon,
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
                    let toks = lex(&c.text, line, names);
                    // A call to an undeclared name is refused by `sentence` at this line, so the core refuses the line as a form it cannot read.
                    if names.bad_calls.contains_key(&line) {
                        (CondKind::Bad(Refusal::Syntax(line)), Expr::Int(0))
                    } else {
                        match parse_contract(&toks, line) {
                            Ok(e) => (want, e),
                            Err(r) => (CondKind::Bad(r), Expr::Int(0)),
                        }
                    }
                }
                word => (CondKind::Other(names.id(word)), Expr::Int(0)),
            }
        };
        items.push((kind, e, line, param_names(c.params, names)));
    }
    items.into_iter().rev().fold(Conds::Nil, |rest, (k, e, l, p)| Conds::Cons(k, e, l, p, Box::new(rest)))
}

// ------------------------------------------------------------------ the companion file

/// The keywords of Dafny 4.11 that a companion file may not hold, decisions 0080 and 0099. The words that it may hold are `function`, `predicate`,
/// `lemma`, `assert`, `ghost`, `requires`, `ensures`, `decreases`, `reads`, `if`, `then`, `else`, `var`, `match`, `case`, `forall`, `exists`, `true`, `false`,
/// `as`, `is`, `in`, `int`, `nat`, `bool`, `seq`, `set`, `map` and `multiset`.
const BANNED: &[&str] = &[
    "abstract", "allocated", "assume", "break", "by", "calc", "char", "class", "codatatype", "colemma", "comethod", "const", "constructor",
    "continue", "copredicate", "datatype", "default", "expect", "export", "extends", "fresh", "greatest", "imap", "import", "include", "inductive",
    "invariant", "iset", "iterator", "label", "least", "method", "modifies", "modify", "module", "nameonly", "new", "newtype", "null", "object",
    "old", "opaque", "opened", "ORDINAL", "print", "provides", "real", "refines", "return", "returns", "reveal", "reveals", "static", "string", "this",
    "to", "trait", "twostate", "type", "unchanged", "while", "witness", "yield", "yields",
];

/// The names of the prelude. A companion file may not declare them, nor a name with a prefix of the model, decision 0083.
const MODEL_NAMES: &[&str] = &["Option", "Some", "None", "Vec", "value", "int32", "int64", "uint8", "uint32", "uint64"];

/// The sentence for a word of a companion file that is not allowed.
fn only_functions(word: &str) -> String {
    format!("{word}: a companion file can hold only functions, predicates and lemmas.")
}

/// A declaration of the companion file: its name, the line of the name, and whether it is a lemma.
type Declared = (String, u32, bool);

/// The refusals of a companion file as (line, sentence), and the declarations it holds, decision 0080. The scan reads comments as Dafny does:
/// `//` to the end of the line, and `/* */` that nest. It refuses a comment that does not end, each `"`, `@` and `{:`, and each keyword of
/// Dafny that is not on the short list. Each word is refused once for each line. The file holds nothing else than `function`, `predicate`
/// and `lemma` declarations then, and a file with a refusal declares no name.
// ponytail: a string is skipped to the next quote on its line, because the file is refused at the quote anyway. A file with no quote
// has no string. Upgrade: the lexer in the core, decision 0077.
fn scan_companion(text: &str) -> (Vec<(u32, String)>, Vec<Declared>) {
    // The bytes first, decision 0083. Dafny ends a line at a carriage return alone, so the lines below are those of a file with no lone one.
    let mut bad = Vec::new();
    let mut line = 1u32;
    let mut chars = text.chars().peekable();
    while let Some(c) = chars.next() {
        match c {
            '\n' => line += 1,
            '\r' if chars.peek() == Some(&'\n') => {}
            ' '..='~' | '\t' => {}
            _ => bad.push((line, "a character that a companion file cannot hold.".to_string())),
        }
    }
    bad.dedup();
    if !bad.is_empty() {
        return (bad, Vec::new());
    }
    let (mut refused, mut declared) = (Vec::new(), Vec::new());
    let mut depth = 0usize;
    let mut opened = 0u32;
    // The word before the name: 0 none, 1 `function` or `predicate`, 2 `lemma`.
    let mut after_decl = 0u8;
    for (n, line) in text.lines().enumerate() {
        let n = n as u32 + 1;
        let mut rest = line;
        while let Some(c) = rest.chars().next() {
            let mut used = c.len_utf8();
            // A comment does not part a name from `function`.
            let in_comment = depth > 0 || rest.starts_with("/*");
            if depth > 0 {
                if rest.starts_with("/*") {
                    depth += 1;
                    used = 2;
                } else if rest.starts_with("*/") {
                    depth -= 1;
                    used = 2;
                }
            } else if rest.starts_with("//") {
                break;
            } else if rest.starts_with("/*") {
                if depth == 0 {
                    opened = n;
                }
                depth += 1;
                used = 2;
            } else if c.is_ascii_alphabetic() || c == '_' || c == '?' {
                used = rest.find(|ch: char| !(ch.is_ascii_alphanumeric() || matches!(ch, '_' | '\'' | '?'))).unwrap_or(rest.len());
                let w = &rest[..used];
                if after_decl != 0 {
                    if MODEL_NAMES.contains(&w) || ["v_", "c_", "S_", "f_", "b_", "trunc_"].iter().any(|p| w.starts_with(p)) {
                        refused.push((n, format!("{w}: a name that the model uses.")));
                    }
                    declared.push((w.to_string(), n, after_decl == 2));
                }
                after_decl = match w {
                    "function" | "predicate" => 1,
                    "lemma" => 2,
                    _ => 0,
                };
                if BANNED.contains(&w) {
                    refused.push((n, only_functions(w)));
                }
                rest = &rest[used..];
                continue;
            } else if c.is_ascii_digit() {
                // A run of digits ends where a letter starts, so `1newtype` is the number 1 and the word newtype.
                used = rest.find(|ch: char| !ch.is_ascii_digit()).unwrap_or(rest.len());
            } else if c == '"' {
                refused.push((n, only_functions("\"")));
                let mut skip = 1;
                let mut chars = rest[1..].chars();
                while let Some(d) = chars.next() {
                    skip += d.len_utf8();
                    if d == '\\' {
                        skip += chars.next().map_or(0, char::len_utf8);
                    } else if d == '"' {
                        break;
                    }
                }
                used = skip.min(rest.len());
            } else if c == '@' {
                refused.push((n, only_functions("@")));
            } else if rest.starts_with("{:") {
                refused.push((n, only_functions("{:")));
                used = 2;
            }
            if !c.is_whitespace() && !in_comment {
                after_decl = 0;
            }
            rest = &rest[used..];
        }
    }
    if depth > 0 {
        refused.push((opened, "a comment that does not end.".to_string()));
    }
    refused.sort();
    refused.dedup();
    if refused.is_empty() {
        (refused, declared)
    } else {
        (refused, Vec::new())
    }
}

// ------------------------------------------------------------------ names that Dafny can read

/// Every name in an expression that the Dafny text will print.
fn expr_names<'a>(e: &'a JExpr, out: &mut Vec<&'a str>) {
    match e {
        JExpr::Var(v, _) => out.push(v),
        JExpr::Bin(_, a, b) | JExpr::Divide(_, a, b, _) | JExpr::Index(a, b) | JExpr::Subspan(a, b) => {
            expr_names(a, out);
            expr_names(b, out);
        }
        JExpr::Cond(c, a, b) => {
            expr_names(c, out);
            expr_names(a, out);
            expr_names(b, out);
        }
        JExpr::Not(a) | JExpr::Neg(a) | JExpr::Cast(_, a) | JExpr::Paren(a) | JExpr::Brace(a) | JExpr::Size(a) | JExpr::Empty(a) | JExpr::Copy(a, ..) | JExpr::Field(a, _) | JExpr::HasValue(a) | JExpr::Value(a) | JExpr::Wrap(a) => expr_names(a, out),
        JExpr::Call(_, _, args, _) | JExpr::Construct(_, args) => args.iter().for_each(|a| expr_names(a, out)),
        JExpr::Lit(..) | JExpr::Bool(_) | JExpr::Nullopt | JExpr::Unknown(..) => {}
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

fn function(f: JFunction, names: &mut Names) -> Function {
    let name = names.id(&f.key);
    names.file = f.file;
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
    let params = ps.into_iter().rev().fold(Params::Nil, |rest, (n, t)| Params::Cons(n, t, Box::new(rest)));
    let ret = ty(f.ret, names);
    let line = names.here(f.line);
    Function { name, line, params, ret, trusted: f.trusted.is_some(), conds: conds(f.conds, names), body: stmts(f.body, names) }
}

// ------------------------------------------------------------------ the Dafny text

pub const PRELUDE: &str = r"newtype int32 = x: int | -0x8000_0000 <= x < 0x8000_0000
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
        DTy::Bool => "bool".to_string(),
        DTy::Seq(s) => format!("Vec<{}>", dscalar(s, names)),
        DTy::Struct(k) => names.datatypes[&k].clone(),
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
    while let DArgs::Cons(a, next) = rest {
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
        DExpr::Ctor(k, args) => format!("{}({})", names.datatypes[k], dargs(args, names).join(", ")),
        DExpr::Len(a) => format!("|{}|", dexpr(a, names)),
        DExpr::Index(a, i) => format!("{}[{}]", dexpr(a, names), dexpr(i, names)),
        DExpr::Drop(a, k) => format!("{}[{}..]", dexpr(a, names), dexpr(k, names)),
        DExpr::Take(a, j) => format!("{}[..{}]", dexpr(a, names), dexpr(j, names)),
        DExpr::Slice(a, i, j) => format!("{}[{}..{}]", dexpr(a, names), dexpr(i, names), dexpr(j, names)),
        // The prefix `b_` keeps a bound name apart from `v_` and `c_` names.
        DExpr::Forall(j, b) => format!("(forall b_{}: int :: {})", names.text(*j), dexpr(b, names)),
        DExpr::Exists(j, b) => format!("(exists b_{}: int :: {})", names.text(*j), dexpr(b, names)),
        DExpr::Bound(j) => format!("b_{}", names.text(*j)),
        DExpr::Apply(f, args) => format!("{}({})", names.text(*f), dargs(args, names).join(", ")),
        DExpr::After => "v_this'".to_string(),
        DExpr::FCall(k, args) => format!("{}({})", names.functions[k], dargs(args, names).join(", ")),
        DExpr::TDiv(a, b) => format!("trunc_div({}, {})", dexpr(a, names), dexpr(b, names)),
        DExpr::TRem(a, b) => format!("trunc_rem({}, {})", dexpr(a, names), dexpr(b, names)),
        DExpr::DivIn(a, b, t) => format!("(trunc_div({}, {}) as {})", dexpr(a, names), dexpr(b, names), dty(*t, names)),
        // The let checks that the quotient fits T before it gives the remainder, as C++ requires. `q'` cannot clash with a C++ name.
        DExpr::RemIn(a, b, t) => {
            let (a, b, t) = (dexpr(a, names), dexpr(b, names), dty(*t, names));
            format!("(var q' := (trunc_div({a}, {b}) as {t}); (trunc_rem({a}, {b}) as {t}))")
        }
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

    /// The Dafny name of the object that a call writes back, and the call `m(o, args)`.
    fn update(&self, obj: Obj, m: u32, args: &DArgs) -> (String, String) {
        let object = match obj {
            Obj::Local(n) => mangle(self.names.text(n)),
            Obj::Object => "v_this'".to_string(),
        };
        let shown = std::iter::once(object.clone()).chain(dargs(args, self.names)).collect::<Vec<_>>().join(", ");
        (object, format!("{}({shown})", self.methods[&m]))
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
            // Dafny's `return e;` would need both out-parameters of a method that writes its object.
            DStmt::Return(e) if self.writes => {
                self.put(depth, format!("result := {};", dexpr(e, names)), place);
                self.put(depth, "return;".to_string(), place);
            }
            DStmt::Return(e) => self.put(depth, format!("return {};", dexpr(e, names)), place),
            DStmt::SetField(f, e) => self.put(depth, format!("v_this' := v_this'.(f_{} := {});", names.text(*f), dexpr(e, names)), place),
            DStmt::Update(obj, m, args) => {
                let (object, call) = self.update(*obj, *m, args);
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
            DStmt::LocalUpdate(x, t, obj, m, args) => {
                let (object, call) = self.update(*obj, *m, args);
                let x = mangle(names.text(*x));
                self.put(depth, format!("var {x}: {}; {x}, {object} := {call};", dty(*t, names)), place);
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
                while let DCalls::Cons(t, ty, m, args, next) = rest {
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
    /// A method that gives no value has no `result`. One that writes its object also gives it back as `this'`, of the type of its first
    /// parameter, decision 0096.
    fn header(&mut self, name: u32, params: &DParams, ret: DTy, (writes, axiom): (bool, bool), place: u32) {
        let mut shown = Vec::new();
        let mut ps = params;
        while let DParams::Cons(n, t, next) = ps {
            shown.push(format!("{}: {}", mangle(self.names.text(*n)), dty(*t, self.names)));
            ps = next;
        }
        let mut gives = Vec::new();
        if ret != DTy::Void {
            gives.push(format!("result: {}", dty(ret, self.names)));
        }
        if let (true, DParams::Cons(_, t, _)) = (writes, params) {
            gives.push(format!("v_this': {}", dty(*t, self.names)));
        }
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
        while let DParams::Cons(n, t, next) = ps {
            shown.push(format!("{}: {}", mangle(self.names.text(*n)), dty(*t, self.names)));
            ps = next;
        }
        self.out.push('\n');
        self.lines.push(None);
        self.put(0, format!("function {}({}): {}", self.names.functions[&m.name], shown.join(", "), dty(m.ret, self.names)), place);
        let mut cs = &m.requires;
        while let DConds::Cons(e, line, next) = cs {
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
        self.header(m.name, &m.params, m.ret, (m.writes, m.trusted), place);
        self.temps = 0;
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
        // A trusted method has no body, and Dafny takes its contract as given, decision 0102.
        if m.trusted {
            self.scope.clear();
            return;
        }
        self.put(0, "{".to_string(), place);
        self.writes = m.writes;
        if m.writes {
            self.put(1, "v_this' := v_this;".to_string(), place);
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
            "a call out of place. The translator takes a call when C++ runs it once and the statement uses its value. It takes a call that writes its object or gives no value only alone.".to_string(),
        ),
        Refusal::Twice(n, line) => (line, format!("{} is declared twice in the function.", names.text(n))),
        Refusal::Convert(line) => (line, "a conversion between bool and a number.".to_string()),
        Refusal::WriteParam(n, line) => (line, format!("{} is a parameter. The translator writes only a local.", names.text(n))),
        Refusal::NoVar(n, line) => (line, format!("{} in the {} line is no variable.", names.text(n), names.contracts.get(&line).map_or("contract", |c| c.0.as_str()))),
        Refusal::SeqParam(line) => (line, "a sequence is in the subset only as a parameter.".to_string()),
        Refusal::HoldsSeq(line) => (line, "a struct that holds a sequence is in the subset only as a parameter.".to_string()),
        Refusal::Element(line) => (line, "an optional of a struct or a sequence of bool has no rule yet.".to_string()),
        Refusal::Extent(line) => (line, "a sequence or an optional made from one of another type or length.".to_string()),
        Refusal::NoTarget(line) => (line, "the call writes its object, and the translator writes back only a local.".to_string()),
        Refusal::NoObject(n, line) => (line, format!("{} is a member of the struct. A requires line of a constructor has no object yet.", names.text(n))),
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
pub fn translate(lines: &str, companion: Option<(&str, &str)>) -> Result<Translation> {
    // The text `operator()` is the first word, so its id is `CALL_OP`, the id that the core uses, decision 0098.
    let mut names = Names { words: vec!["operator()".to_string()], ..Default::default() };
    let mut refusals = Vec::new();
    let mut funcs = Vec::new();
    let mut structs = Vec::new();
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
    // ponytail: a struct that holds a struct refused for its name is not caught. Upgrade: close the set under the fields.
    // A dropped function shows its other defects only after the struct is renamed.
    let mut items = Vec::new();
    for l in lines.lines().filter(|l| !l.trim().is_empty()) {
        items.push((serde_json::from_str(l).with_context(|| format!("cannot read a line of the tree: {l}"))?, l));
    }
    let unreadable_keys: Vec<String> =
        items.iter().filter_map(|(i, _)| if let Item::Struct(st) = i { unreadable_struct_name(st).map(|_| serde_json::to_string(&st.key).unwrap_or_default()) } else { None }).collect();
    for (item, l) in items {
        match item {
            Item::Orphan { orphan, file, word } => {
                let said = if word == "assert" || word == "apply" { "an assert or apply line needs a statement below it in its block." } else { "a contract line that belongs to no function." };
                refusals.push((file, orphan, said.to_string()));
            }
            Item::Struct(st) => structs.push(st),
            Item::Function(_) if unreadable_keys.iter().any(|k| l.contains(k.as_str())) => {}
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
        at.insert(key, names.place(&f.file, f.line));
        if let Some((reason, file, line)) = &f.trusted {
            reasons.insert(key, (file.clone(), *line, f.name.clone(), reason.clone()));
        }
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
        let fields = st.fields.into_iter().rev().fold(Params::Nil, |rest, (n, t)| Params::Cons(names.id(&n), ty(t, &mut names), Box::new(rest)));
        // The core marks which members are pure and their types, so the shell writes `None`.
        let members = st.members.into_iter().rev().fold(Members::Nil, |rest, (n, k)| Members::Cons(names.id(&n), names.id(&k), None, Box::new(rest)));
        table = Structs::Cons(key, place, fields, members, Box::new(table));
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
    while let Models::Cons(model, next) = seen {
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
    for (place, unreadable) in struct_places {
        let StructModels::Cons(model, rest) = smodels else { unreachable!("one model for each struct") };
        match model {
            // The struct is refused, and its callers keep the type. The refusal stands for the file.
            Ok(_) if unreadable.is_some() => refused_at.push((place, format!("{}: a name with a character Dafny cannot read.", unreadable.unwrap_or_default()))),
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
    let mut printed = 0;
    let mut trusted = Vec::new();
    for _ in 0..count {
        let Models::Cons(model, rest) = models else { unreachable!("one model for each function") };
        let refused = match model {
            Model::Full(m) => {
                p.method(&m, at[&m.name]);
                printed += 1;
                trusted.extend(reasons.remove(&m.name).filter(|_| m.trusted));
                None
            }
            Model::Bare(key, params, ret, r) => {
                p.header(key, &params, ret, (writing.contains(&key), false), at[&key]);
                printed += 1;
                Some(r)
            }
            Model::Refused(r) => Some(r),
        };
        refused_at.extend(refused.map(|r| sentence(r, &names)));
        models = *rest;
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
    refusals.sort();
    refusals.dedup();
    Ok(Translation { dafny, methods: printed, trusted, refusals, map: Map { lines, companion: companion_lines, decls, places: names.places, contracts: names.contracts } })
}
