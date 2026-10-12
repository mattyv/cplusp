//! The `cplusp` command line. It parses files, runs clang-tidy and prints text.
//! Every policy decision comes from `cplusp_core`. See docs/policy.md.

mod model;
mod prove;

use std::collections::{BTreeMap, HashSet};
use std::fs;
use std::io::ErrorKind;
use std::path::{Path, PathBuf};
use std::process::{Command, ExitCode, Stdio};

use anyhow::{anyhow, bail, Context, Result};
use cplusp_core::flags::FlagFault;
use clap::{Args, Parser, Subcommand};
use cplusp_core::{
    apply_overrides, emit, is_active, keep_finding, kind_at, rule_by_id, rule_for_check, validate, CheckOption, CheckRef, Config, Decision,
    Kind, Override, Policy, PolicyError, Region, Rule,
};
use serde::de::{DeserializeOwned, IgnoredAny};
use serde::Deserialize;

/// The default policy lives in the binary, so `extends` works from any directory.
const DEFAULT_POLICY: &str = include_str!("../../../policy/cplusp-policy.yaml");

/// Compiler diagnostics are not in `clang-tidy --list-checks`. Their names start like this.
const DIAGNOSTIC: &str = "clang-diagnostic-";

/// What clang-tidy names the diagnostic of a check that is given a bad option.
const CONFIG_ERROR: &str = "clang-tidy-config";

/// The check of the plugin that writes the tree of each function as JSON, decisions 0056 and 0057. Only the `model` command enables it.
const TREE: &str = "cplusp-tree";

/// The generic check of the plugin. A `matcher` entry of the policy becomes an option of this check.
const MATCHER: &str = "cplusp-matcher";

/// The allowlist check of the plugin. It claims the kinds of a ban row for the row, and a team may loosen that row.
const ALLOWLIST: &str = "cplusp-allowlist";

/// The check of the plugin that reports every `#line` and line marker the preprocessor processed. Its findings belong to no row of the
/// policy. The gate enables it for every run and reports them under the rule `line`.
const LINE_DIRECTIVE: &str = "cplusp-line-directive";

/// The check of the plugin that reports every pragma from the preprocessor's callbacks, decision 0038. Like the line directives, its findings
/// belong to no row of the policy. The gate enables it for every run and reports them under the rule `pragma`.
const PRAGMA: &str = "cplusp-pragma";

/// The check of the plugin that reads the markers of include/cplusp.h, decisions 0039 and 0047. The gate enables it for every run. It
/// reports in four forms. All offsets are clang-tidy's own `FileOffset`, as for every finding, and an end is one past the last byte.
/// A region is the body of a function the file writes, or a plain declaration: `region {verified|trusted|plain} {end offset}`, at the
/// first byte of the region. The gate keeps the regions of a run and shows them to no bot.
/// A call that runs plain code is `reach {qualified name}`, at the call. A use of a plain type, decision 0051, is `uses {qualified name}`, at
/// the use. The gate keeps either when the core gives the place the verified kind.
/// The last form is a finding of the gate's own, `{presumed file}\t{presumed line}\t{sentence}` as for the pragmas. The gate reports
/// it under the rule `marker`.
const MARKERS: &str = "cplusp-markers";

/// The checks of the plugin whose message starts with the id of a rule: `{rule}: {sentence}`, or the bare id. The gate maps a finding
/// to its rule by that id and puts the sentence after the message of the rule. Every other check maps by its own name.
// ponytail: a hand-kept list. Upgrade: a prefix on the check name.
const RULE_FIRST: &[&str] = &[MATCHER, ALLOWLIST, "cplusp-unlisted-state", "cplusp-raw-copy"];

/// Checks that the clang-tidy plugin will add. The policy may name them today.
// ponytail: a hand-kept list. Upgrade: load the plugin and read its `--list-checks`.
const PLANNED_CHECKS: &[&str] = &[
    MATCHER, "cplusp-mutable", "cplusp-multiple-inheritance", "cplusp-iterator-arithmetic", "cplusp-impure-operator", "cplusp-lambda-limits",
    "cplusp-evaluation-order", "cplusp-inexact-literal", "cplusp-raw-copy", "cplusp-aliasing", "cplusp-const-handle", "cplusp-allowlist", "cplusp-unlisted-state",
    "cplusp-indirect-call", LINE_DIRECTIVE, PRAGMA,
];

// ------------------------------------------------------------------ command line

#[derive(Parser)]
enum Cli {
    /// Work with the policy file.
    Policy {
        #[command(subcommand)]
        cmd: PolicyCmd,
    },
    /// Run clang-tidy under the policy. Exit 1 if a finding stands.
    Gate {
        #[command(flatten)]
        common: Common,
        /// One JSON object per finding, one per line.
        #[arg(long)]
        json: bool,
        /// Build directory with compile_commands.json, passed to clang-tidy.
        #[arg(short = 'p')]
        build_dir: Option<PathBuf>,
        /// The clang-tidy plugin, built from clang-tidy/. Loaded into clang-tidy for the run.
        #[arg(long)]
        plugin: Option<PathBuf>,
        #[arg(required = true)]
        files: Vec<PathBuf>,
        /// Compiler arguments, after `--`.
        #[arg(last = true)]
        clang_args: Vec<String>,
    },
    /// Translate the functions of a file to Dafny, decisions 0056 and 0057. Exit 1 if a function is refused.
    Model {
        /// The clang-tidy plugin, built from clang-tidy/.
        #[arg(long)]
        plugin: Option<PathBuf>,
        /// The Dafny file to write. It is written even when a function is refused.
        #[arg(long)]
        out: PathBuf,
        file: PathBuf,
        /// Compiler arguments, after `--`.
        #[arg(last = true)]
        clang_args: Vec<String>,
    },
    /// Run the gate, translate the functions to Dafny, and run the prover, decision 0068. Exit 1 if something is refused or not proved.
    Prove {
        #[command(flatten)]
        common: Common,
        /// The clang-tidy plugin, built from clang-tidy/.
        #[arg(long)]
        plugin: Option<PathBuf>,
        /// Seconds for each method.
        #[arg(long, default_value_t = 20)]
        time_limit: u32,
        file: PathBuf,
        /// Compiler arguments, after `--`.
        #[arg(last = true)]
        clang_args: Vec<String>,
    },
}

#[derive(Subcommand)]
enum PolicyCmd {
    /// Validate the policy. Exit 2 on a problem.
    Check(Common),
    /// Print the clang-tidy config the policy generates.
    Emit(Common),
    /// Print the policy as a fixed-width table.
    Show(Common),
    /// Print the policy as the markdown table of docs/plan.md.
    Doc(Common),
}

#[derive(Args)]
struct Common {
    /// A team policy. The default policy when absent.
    #[arg(long)]
    policy: Option<PathBuf>,
}

// ponytail: `println!` panics on a closed pipe, as in `cplusp policy show | head`.
// Upgrade: write through a locked handle and ignore `BrokenPipe`.
fn main() -> ExitCode {
    match run(Cli::parse()) {
        Ok(code) => code,
        Err(e) => {
            eprintln!("{e:#}");
            ExitCode::from(2)
        }
    }
}

fn run(cli: Cli) -> Result<ExitCode> {
    match cli {
        Cli::Policy { cmd } => {
            let (PolicyCmd::Check(c) | PolicyCmd::Emit(c) | PolicyCmd::Show(c) | PolicyCmd::Doc(c)) = &cmd;
            let listed = locate(TIDY).map(|tool| list_checks(&tool, None)).transpose()?;
            if listed.is_none() && matches!(cmd, PolicyCmd::Check(_)) {
                bail!("clang-tidy not found. Check names cannot be validated.");
            }
            let loaded = load(c.policy.as_deref(), listed.as_deref())?;
            match cmd {
                PolicyCmd::Check(_) => {
                    let enforced = loaded.policy.rules.iter().filter(|r| is_active(r)).count();
                    println!("ok: {} rules, {enforced} enforced by the gate", loaded.policy.rules.len());
                }
                PolicyCmd::Emit(_) => print!("{}", config_text(&emit(&loaded.policy))),
                PolicyCmd::Show(_) => show(&loaded),
                PolicyCmd::Doc(_) => doc(&loaded),
            }
            Ok(ExitCode::SUCCESS)
        }
        Cli::Gate { common, json, build_dir, plugin, files, clang_args } => {
            gate(&common, json, build_dir.as_deref(), plugin.as_deref(), &files, &clang_args)
        }
        Cli::Model { plugin, out, file, clang_args } => model(plugin.as_deref(), &out, &file, &clang_args),
        Cli::Prove { common, plugin, time_limit, file, clang_args } => prove(&common, plugin.as_deref(), time_limit, &file, &clang_args),
    }
}

// ----------------------------------------------------------------- policy file

/// Which part of the toolchain guarantees a row.
#[derive(Clone, Copy, PartialEq, Debug, Deserialize)]
#[serde(rename_all = "lowercase")]
enum Stage {
    Gate,
    Prover,
    Spec,
    None,
}

/// The core's `Decision`, read from the words of the file.
#[derive(Deserialize)]
#[serde(remote = "Decision", rename_all = "snake_case")]
enum DecisionWords {
    Allow,
    Restrict,
    TrustedOnly,
    Ban,
}

/// A policy file. `R` is a full rule, or an override when the file extends the default policy.
#[derive(Deserialize)]
struct File<R> {
    extends: Option<String>,
    rules: Vec<R>,
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct Entry {
    id: String,
    construct: String,
    area: String,
    canonical: Option<String>,
    #[serde(with = "DecisionWords")]
    decision: Decision,
    limit: Option<String>,
    why: String,
    use_instead: Option<String>,
    stage: Option<Stage>,
    #[serde(default)]
    detect: Vec<Detect>,
}

/// One `detect` entry: `check` with optional `options`, or `matcher`.
#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct Detect {
    check: Option<String>,
    #[serde(default)]
    options: BTreeMap<String, String>,
    matcher: Option<String>,
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct Ov {
    id: String,
    #[serde(with = "DecisionWords")]
    decision: Decision,
    limit: Option<String>,
    loosened_because: Option<String>,
}

/// The fields of a rule that the core does not hold.
struct Doc {
    construct: String,
    canonical: Option<String>,
    stage: Stage,
}

/// A valid policy. `docs[i]` belongs to `policy.rules[i]`.
struct Loaded {
    policy: Policy,
    docs: Vec<Doc>,
}

fn parse<T: DeserializeOwned>(text: &str, what: &str) -> Result<T> {
    serde_yaml::from_str(text).with_context(|| format!("cannot parse {what}"))
}

/// The `detect` list of a rule, as the core reads it. A `matcher` becomes an option of `cplusp-matcher`,
/// named `{id}/{n}` for the rule's n-th pattern. The plugin reads the rule id from that name.
fn detect_refs(id: &str, detect: Vec<Detect>) -> Result<Vec<CheckRef>> {
    let mut patterns = 0;
    detect
        .into_iter()
        .map(|d| match d {
            Detect { check: Some(name), options, matcher: None } => {
                Ok(CheckRef { name, options: options.into_iter().map(|(key, value)| CheckOption { key, value }).collect() })
            }
            Detect { check: None, options, matcher: Some(value) } if options.is_empty() => {
                patterns += 1;
                Ok(CheckRef { name: MATCHER.to_string(), options: vec![CheckOption { key: format!("{id}/{patterns}"), value }] })
            }
            _ => bail!("{id}: a detect entry is a check with options, or a matcher alone"),
        })
        .collect()
}

fn build(entries: Vec<Entry>) -> Result<Loaded> {
    let (mut rules, mut docs) = (Vec::new(), Vec::new());
    for e in entries {
        // A row without a stage is the gate's, unless it is an allow row with no checks.
        // A ban row that names no checks must reach `validate`, so it cannot default to `none`.
        let stage = e.stage.unwrap_or(if e.decision == Decision::Allow && e.detect.is_empty() { Stage::None } else { Stage::Gate });
        // A row with checks is the gate's even if the prover owns it today. Its checks are
        // dormant under `allow`, and a team override to `ban` turns them on.
        let gate = stage == Stage::Gate || !e.detect.is_empty();
        let detect = detect_refs(&e.id, e.detect)?;
        rules.push(Rule {
            gate,
            id: e.id,
            area: e.area,
            decision: e.decision,
            limit: e.limit,
            why: e.why,
            use_instead: e.use_instead,
            detect,
            loosened_because: None,
        });
        docs.push(Doc { construct: e.construct, canonical: e.canonical, stage });
    }
    Ok(Loaded { policy: Policy { rules }, docs })
}

/// Load the policy file, or the default policy. The core validates it.
/// `listed` is the check list of clang-tidy. Without one, check names are not validated.
fn load(path: Option<&Path>, listed: Option<&[String]>) -> Result<Loaded> {
    let what = path.map_or("the default policy".to_string(), |p| p.display().to_string());
    let text = match path {
        Some(p) => fs::read_to_string(p).with_context(|| format!("cannot read {what}"))?,
        None => DEFAULT_POLICY.to_string(),
    };
    let loaded = match parse::<File<IgnoredAny>>(&text, &what)?.extends.as_deref() {
        None => {
            let loaded = build(parse::<File<Entry>>(&text, &what)?.rules)?;
            check(&loaded.policy, listed)?;
            loaded
        }
        Some("cplusp:default") => {
            let base = build(parse::<File<Entry>>(DEFAULT_POLICY, "the default policy")?.rules)?;
            // `apply_overrides` needs unique ids in its base, so the base is validated first.
            check(&base.policy, listed)?;
            let overrides: Vec<Override> = parse::<File<Ov>>(&text, &what)?
                .rules
                .into_iter()
                .map(|o| Override { id: o.id, decision: o.decision, limit: o.limit, loosened_because: o.loosened_because })
                .collect();
            let policy = apply_overrides(&base.policy, &overrides).map_err(|e| anyhow!(problems(&e, &base.policy)))?;
            check(&policy, listed)?;
            Loaded { policy, docs: base.docs }
        }
        Some(other) => bail!("{what}: cannot extend `{other}`. Use `cplusp:default`."),
    };
    for r in &loaded.policy.rules {
        if let Some(why) = &r.loosened_because {
            eprintln!("loosened: {}. {why}", r.id);
        }
    }
    if listed.is_none() {
        eprintln!("warning: clang-tidy not found. Check names are not validated.");
    }
    Ok(loaded)
}

/// The `name` of a `clang-diagnostic-{name}` check becomes `-W{name}` in the config, so it must be a warning flag.
/// Not `error`, which makes every warning an error. Not `no-...`, which switches a warning off. No other characters.
fn is_warning_flag(name: &str) -> bool {
    name != "error" && !name.starts_with("no-") && !name.is_empty() && name.chars().all(|c| c.is_ascii_lowercase() || c.is_ascii_digit() || c == '-')
}

/// Run the core's validation. `listed` is the clang-tidy check list, if there is one.
fn check(policy: &Policy, listed: Option<&[String]>) -> Result<()> {
    let used = policy.rules.iter().flat_map(|r| &r.detect).map(|c| c.name.clone()).filter(|n| n.strip_prefix(DIAGNOSTIC).is_none_or(is_warning_flag));
    let known: Vec<String> = match listed {
        // ponytail: `--list-checks` omits compiler diagnostics, so any `clang-diagnostic-` name with the shape of a warning passes.
        // Upgrade: validate it against clang's warning list.
        Some(list) => list
            .iter()
            .cloned()
            .chain(PLANNED_CHECKS.iter().map(|c| c.to_string()))
            .chain(used.filter(|n| n.starts_with(DIAGNOSTIC)))
            .collect(),
        None => used.collect(),
    };
    let errors = validate(policy, &known);
    if errors.is_empty() {
        return Ok(());
    }
    Err(anyhow!(problems(&errors, policy)))
}

/// One line per error, as `{id}: {problem}`.
fn problems(errors: &[PolicyError], policy: &Policy) -> String {
    let word = |id: &str| policy.rules.iter().find(|r| r.id == id).map_or("rule", |r| decision_word(r.decision));
    let lines: Vec<String> = errors
        .iter()
        .map(|e| match e {
            PolicyError::RestrictWithoutLimit { id } => format!("{id}: restrict needs a limit"),
            PolicyError::MissingDetect { id } => format!("{id}: {} needs detect", word(id)),
            PolicyError::MissingUseInstead { id } => format!("{id}: {} needs use_instead", word(id)),
            PolicyError::DuplicateId { id } => format!("{id}: duplicate id"),
            PolicyError::UnknownCheck { id, check } => format!("{id}: check {check} is not known"),
            PolicyError::UnknownOverrideId { id } => format!("{id}: unknown rule in override"),
            PolicyError::LoosenedWithoutReason { id } => format!("{id}: loosened without loosened_because"),
        })
        .collect();
    lines.join("\n")
}

fn decision_word(d: Decision) -> &'static str {
    match d {
        Decision::Allow => "allow",
        Decision::Restrict => "restrict",
        Decision::TrustedOnly => "trusted_only",
        Decision::Ban => "ban",
    }
}

// ------------------------------------------------------------------ text output

fn config_text(c: &Config) -> String {
    let checks: String = c.checks.iter().map(|k| format!(",{k}")).collect();
    let mut text = format!("# Generated by cplusp from cplusp-policy.yaml. Do not edit.\nChecks: '-*{checks}'\nWarningsAsErrors: '*'\nHeaderFilterRegex: '.*'\n");
    // clang reports `clang-diagnostic-{name}` only with `-W{name}` on, and leaves some of them off.
    let warnings: Vec<String> = c.checks.iter().filter_map(|k| k.strip_prefix(DIAGNOSTIC)).map(|n| format!("'-W{n}'")).collect();
    if !warnings.is_empty() {
        text += &format!("ExtraArgs: [{}]\n", warnings.join(", "));
    }
    if !c.options.is_empty() {
        text += "CheckOptions:\n";
        for o in &c.options {
            text += &format!("  {}.{}: '{}'\n", o.check, o.key, o.value.replace('\'', "''"));
        }
    }
    text
}

fn show(loaded: &Loaded) {
    // ponytail: fixed widths for the first four columns. A longer value pushes its row out of line.
    // Upgrade: size each column to its longest value.
    let limits = loaded.policy.rules.iter().filter_map(|r| r.limit.as_ref());
    let w = limits.map(|l| l.chars().count()).max().unwrap_or(0).max(5);
    let row = |a: &str, b: &str, c: &str, d: &str, e: &str, f: &str| {
        println!("{}", format!("{a:<12} {b:<28} {c:<13} {d:<8} {e:<w$} {f}").trim_end())
    };
    row("area", "id", "decision", "stage", "limit", "note");
    for (r, d) in loaded.policy.rules.iter().zip(&loaded.docs) {
        let (stage, note) = (format!("{:?}", d.stage).to_lowercase(), if r.loosened_because.is_some() { "loosened" } else { "" });
        row(&r.area, &r.id, decision_word(r.decision), &stage, r.limit.as_deref().unwrap_or(""), note);
    }
}

fn doc(loaded: &Loaded) {
    println!("| Area | Construct | Canonical stance | Why, for us | Decision | Stage |");
    println!("| --- | --- | --- | --- | --- | --- |");
    for (r, d) in loaded.policy.rules.iter().zip(&loaded.docs) {
        let mut area = r.area.chars();
        let area = area.next().map(|f| f.to_uppercase().collect::<String>() + area.as_str()).unwrap_or_default();
        let decision = match r.decision {
            Decision::Allow => "Allow".to_string(),
            Decision::Ban => "Ban".to_string(),
            Decision::TrustedOnly => "Trusted only".to_string(),
            Decision::Restrict => format!("Restrict: {}", r.limit.as_deref().unwrap_or("")),
        };
        let stage = if d.stage == Stage::None { "—".to_string() } else { format!("{:?}", d.stage) };
        println!("| {area} | {} | {} | {} | {decision} | {stage} |", d.construct, d.canonical.as_deref().unwrap_or(""), r.why);
    }
}

// ------------------------------------------------------------------ build flags

/// The sentence for a refused flag, decision 0128.
fn flag_reason(fault: FlagFault) -> &'static str {
    match fault {
        FlagFault::Float => "It changes floating-point results, and the proofs assume IEEE 754 round to nearest.",
        FlagFault::Std => "The proofs assume C++23 or later.",
        FlagFault::Reads => "It changes what the compiler reads or reports, and the gate runs the compiler itself.",
        FlagFault::ResponseFile => "The gate cannot read a response file.",
        FlagFault::ConfigFile => "The gate cannot read a config file.",
        FlagFault::HidesAll => "It hides the compiler warnings the policy names.",
        FlagFault::HidesRow => "It hides a compiler warning the policy names.",
        FlagFault::Swallows => "It takes the next flag as its value, and the gate reads the flags as written.",
    }
}

/// One message for each trailing flag the proofs cannot follow, and for each flag the gate needs and does not find. The core judges the flags,
/// decision 0128, and the shell writes the sentences.
/// `checks` is the check list of the generated config, so a `-Wno-{name}` is judged against the rows the policy enables.
// ponytail: the flags are matched as written. Upgrade: ask the compiler for its final flags.
fn refused_flags(flags: &[String], checks: &[String]) -> Vec<String> {
    let bytes = |list: &[String]| list.iter().map(|s| s.as_bytes().to_vec()).collect::<Vec<Vec<u8>>>();
    let check = cplusp_core::flags::check_flags(&bytes(flags), &bytes(checks));
    let mut refused: Vec<String> = check.faults.into_iter().map(|(i, fault)| format!("{}: not allowed with the gate. {}", flags[i], flag_reason(fault))).collect();
    if check.no_std {
        refused.push("no -std flag: the gate needs -std=c++23 or later, because the proofs assume C++23.".to_string());
    }
    if check.no_contract_off {
        refused.push("no -ffp-contract=off: the gate needs it, because the proofs assume no fused multiply-add.".to_string());
    }
    refused
}

// --------------------------------------------------------------------- clang-tidy

const TIDY: [&str; 2] = ["clang-tidy-18", "clang-tidy"];
const CLANG: [&str; 2] = ["clang++-18", "clang++"];

/// The first of `names` that runs.
fn locate(names: [&str; 2]) -> Option<String> {
    let runs = |bin: &str| Command::new(bin).arg("--version").output().is_ok_and(|o| o.status.success());
    names.into_iter().find(|b| runs(b)).map(String::from)
}

/// The clang-tidy option that loads the plugin, if there is one.
fn load_arg(plugin: Option<&Path>) -> Option<String> {
    plugin.map(|p| format!("--load={}", p.display()))
}

/// Every check clang-tidy has, with the plugin loaded when there is one.
fn list_checks(tool: &str, plugin: Option<&Path>) -> Result<Vec<String>> {
    let out = Command::new(tool)
        .args(load_arg(plugin))
        .args(["--list-checks", "-checks=*"])
        .output()
        .with_context(|| format!("cannot run {tool}"))?;
    if !out.status.success() {
        bail!("{tool} --list-checks failed:\n{}", String::from_utf8_lossy(&out.stderr));
    }
    let text = String::from_utf8_lossy(&out.stdout);
    Ok(text.lines().skip_while(|l| !l.starts_with("Enabled checks:")).skip(1).map(|l| l.trim().to_string()).collect())
}

/// The `--export-fixes` file of clang-tidy. It lists findings with and without fixes.
#[derive(Deserialize, Default)]
struct Fixes {
    #[serde(rename = "Diagnostics", default)]
    diagnostics: Vec<Diagnostic>,
}

#[derive(Deserialize)]
struct Diagnostic {
    #[serde(rename = "DiagnosticName")]
    name: String,
    #[serde(rename = "DiagnosticMessage")]
    at: At,
    #[serde(rename = "BuildDirectory", default)]
    dir: String,
}

#[derive(Deserialize)]
struct At {
    #[serde(rename = "FilePath")]
    file: String,
    /// A byte offset.
    #[serde(rename = "FileOffset")]
    offset: usize,
    #[serde(rename = "Message", default)]
    message: String,
}

/// One thing the gate reports. `rule` and `check` are `nolint` or `pragma` for a suppression.
struct Finding {
    path: PathBuf,
    line: usize,
    rule: String,
    check: String,
    decision: Decision,
    message: String,
}

/// An entry of `compile_commands.json`.
#[derive(Deserialize)]
struct DatabaseEntry {
    directory: PathBuf,
    file: PathBuf,
    arguments: Option<Vec<String>>,
    command: Option<String>,
}

/// A file the gate judges, the directory its compiler runs in, and the flags it gets.
type Build = (PathBuf, PathBuf, Vec<String>);

/// The path with `..` and links resolved, when the file exists.
fn same_file(p: &Path) -> PathBuf {
    fs::canonicalize(p).unwrap_or_else(|_| p.to_path_buf())
}

/// A build for every entry of each given file in the database. clang-tidy runs every entry, so the gate judges every entry.
/// The compiler and the file itself are left out of the flags.
// ponytail: a `command` is split on whitespace, and one with a quote or a backslash is refused. Upgrade: a real shell split.
// The database is JSON, which serde_yaml reads. Upgrade: serde_json, when anything else needs it.
fn database_builds(dir: &Path, files: &[PathBuf], cwd: &Path) -> Result<Vec<Build>> {
    let path = dir.join("compile_commands.json");
    let text = fs::read_to_string(&path).with_context(|| format!("cannot read {}", path.display()))?;
    let entries: Vec<DatabaseEntry> = parse(&text, "compile_commands.json")?;
    let mut builds = Vec::new();
    for given in files {
        let file = cwd.join(given);
        let want = same_file(&file);
        let found = builds.len();
        for e in entries.iter().filter(|e| same_file(&e.directory.join(&e.file)) == want) {
            let all = match (&e.arguments, &e.command) {
                (Some(arguments), _) => arguments.clone(),
                (None, Some(command)) if command.contains(['\'', '"', '\\']) => bail!(
                    "{}: the command in compile_commands.json has shell quoting, which the gate cannot read. Use arguments.",
                    given.display()
                ),
                (None, Some(command)) => command.split_whitespace().map(String::from).collect(),
                (None, None) => Vec::new(),
            };
            let flags = all.into_iter().skip(1).filter(|a| same_file(&e.directory.join(a)) != want).collect();
            builds.push((file.clone(), e.directory.clone(), flags));
        }
        if builds.len() == found {
            bail!("{}: no entry in compile_commands.json", given.display());
        }
    }
    Ok(builds)
}

/// A finding the gate makes itself, from a suppression.
fn ban(path: PathBuf, line: usize, rule: &str, message: &str) -> Finding {
    Finding { path, line, rule: rule.to_string(), check: rule.to_string(), decision: Decision::Ban, message: message.to_string() }
}

/// The lines of `text` with a NOLINT. It is a comment, so the preprocessor's output has lost it.
fn nolints(path: &Path, text: &str) -> Vec<Finding> {
    let message = "NOLINT: not allowed in verified code. It silences the gate. Use CPLUSP_TRUSTED with a reason.";
    text.lines().enumerate().filter(|(_, l)| l.contains("NOLINT")).map(|(n, _)| ban(path.to_path_buf(), n + 1, "nolint", message)).collect()
}

/// The flags that name a file the compiler writes. The dependency run drops them, alone or joined to their file name.
// ponytail: a flag that only starts with `-o` goes too, as `-objc`. It matters to no C++ build. Upgrade: ask the compiler for its flags.
const WRITES_A_FILE: [&str; 5] = ["-MF", "-MT", "-MQ", "-MJ", "-o"];

/// The files that the compiler's include graph names for a build. The NOLINT scan reads them: the file itself and every header outside
/// the system directories. The compiler makes the list with `-MM`, from the build's own flags. The flags that write a file are the
/// build's business. This run prints to stdout and writes nothing. A header that a pragma makes system stays in the list.
fn dependencies(clang: &str, (file, dir, flags): &Build, shown: impl Fn(&Path) -> String) -> Result<Vec<PathBuf>> {
    let (mut args, mut rest) = (Vec::new(), flags.iter());
    while let Some(f) = rest.next() {
        if matches!(f.as_str(), "-MD" | "-MMD" | "-MP" | "-c") {
            continue;
        }
        // A flag that names a file takes the next argument when it stands alone, and holds the name when it is joined.
        if let Some(own) = WRITES_A_FILE.iter().find(|own| f.starts_with(**own)) {
            if f == own {
                rest.next();
            }
            continue;
        }
        args.push(f);
    }
    let out = Command::new(clang)
        .current_dir(dir)
        .args(args)
        .args(["-MM", "-MT", "cplusp"])
        .arg(file)
        .stdin(Stdio::null())
        .output()
        .with_context(|| format!("cannot run {clang}"))?;
    if !out.status.success() {
        bail!("cannot preprocess {}: {}", shown(file), String::from_utf8_lossy(&out.stderr).lines().next().unwrap_or_default());
    }
    let list = String::from_utf8_lossy(&out.stdout);
    // The compiler escapes a space, `#` and `$` in a name, and no other white space. A name with a tab or a newline would split in the
    // list, and files named after the pieces could stand in for the header. A line break ends a name only at the end of the rule, or after
    // the backslash that joins two lines.
    let body = list.trim_end_matches('\n');
    let unreadable = body.chars().any(|c| c.is_whitespace() && c != ' ' && c != '\n')
        || body.match_indices('\n').any(|(i, _)| !body[..i].ends_with('\\'));
    if unreadable {
        bail!("cannot preprocess {}: the dependency list holds a name the gate cannot read.", shown(file));
    }
    let paths: Vec<PathBuf> = rule_files(&list).into_iter().map(|p| dir.join(p)).collect();
    if !paths.iter().any(|p| same_file(p) == same_file(file)) {
        bail!("cannot preprocess {}: the dependency list does not name it.", shown(file));
    }
    Ok(paths)
}

/// The files that a make rule names, after its target and colon. A backslash that ends a line joins it with the next. Whitespace splits
/// the names, unless a backslash escapes it. The compiler writes `\ ` for a space, `\#` for `#` and `$$` for `$`.
fn rule_files(rule: &str) -> Vec<String> {
    let after = rule.split_once(':').map_or("", |(_, rest)| rest);
    let (mut files, mut name, mut chars) = (Vec::new(), String::new(), after.chars().peekable());
    let mut flush = |name: &mut String| {
        if !name.is_empty() {
            files.push(std::mem::take(name));
        }
    };
    while let Some(c) = chars.next() {
        match (c, chars.peek()) {
            ('\\', Some('\n')) => {
                chars.next();
                flush(&mut name);
            }
            ('\\', Some(&e @ (' ' | '#'))) => {
                chars.next();
                name.push(e);
            }
            ('$', Some('$')) => {
                chars.next();
                name.push('$');
            }
            (c, _) if c.is_whitespace() => flush(&mut name),
            (c, _) => name.push(c),
        }
    }
    flush(&mut name);
    files
}

fn gate(c: &Common, json: bool, build_dir: Option<&Path>, plugin: Option<&Path>, files: &[PathBuf], clang_args: &[String]) -> Result<ExitCode> {
    if let Some(dir) = build_dir {
        if !clang_args.is_empty() {
            bail!("Use -p or --, not both.");
        }
        if !dir.join("compile_commands.json").exists() {
            bail!("{} has no compile_commands.json", dir.display());
        }
    }
    let tool = locate(TIDY).context("clang-tidy not found. Install clang-tidy-18.")?;
    let listed = list_checks(&tool, plugin)?;
    // clang-tidy ignores a plugin it cannot load, and then every `cplusp-matcher` rule goes quiet.
    if let Some(p) = plugin.filter(|_| !listed.iter().any(|l| l == MATCHER)) {
        bail!("plugin {} did not load. It must provide {MATCHER}.", p.display());
    }
    let loaded = load(c.policy.as_deref(), Some(&listed))?;
    let mut config = emit(&loaded.policy);
    // The plugin reads the line directives and the pragmas from the preprocessor under the build's own flags, for every run.
    // It reads the markers from the tree, for every run too.
    config.checks.push(LINE_DIRECTIVE.to_string());
    config.checks.push(PRAGMA.to_string());
    config.checks.push(MARKERS.to_string());
    // The flags of each file, from after `--` or from the database. Judged before clang-tidy runs.
    let cwd = std::env::current_dir().context("cannot find the working directory")?;
    let builds = match build_dir {
        Some(dir) => database_builds(dir, files, &cwd)?,
        None => files.iter().map(|f| (cwd.join(f), cwd.clone(), clang_args.to_vec())).collect(),
    };
    let mut refused: Vec<String> = Vec::new();
    for (_, _, flags) in &builds {
        for message in refused_flags(flags, &config.checks) {
            if !refused.contains(&message) {
                refused.push(message);
            }
        }
    }
    if !refused.is_empty() {
        bail!("{}", refused.join("\n"));
    }
    let missing: Vec<&str> =
        config.checks.iter().map(String::as_str).filter(|k| !k.starts_with(DIAGNOSTIC) && !listed.iter().any(|l| l == k)).collect();
    if !missing.is_empty() {
        bail!(
            "not enforced: no such check {}. The gate refuses a run that cannot enforce every row. Build the plugin and pass --plugin PATH.",
            missing.join(", ")
        );
    }

    // A NOLINT silences clang-tidy, so it would hide a finding from the gate. It is a finding itself.
    // The scan covers each given file and the headers that the compiler's include graph names outside the system paths.
    let clang = locate(CLANG).context("clang++ not found. Install clang-18.")?;
    let shown = |p: &Path| p.strip_prefix(&cwd).unwrap_or(p).display().to_string();
    let (mut found, mut scanned) = (Vec::new(), HashSet::new());
    let mut scan = |path: PathBuf| -> Result<Vec<Finding>> {
        if !scanned.insert(path.clone()) {
            return Ok(Vec::new());
        }
        let source = fs::read(&path).with_context(|| format!("cannot read {}", shown(&path)))?;
        Ok(nolints(&path, &String::from_utf8_lossy(&source)))
    };
    for build in &builds {
        // The file itself first, so a file that is not there is named before the compiler is asked.
        found.extend(scan(build.0.clone())?);
        for path in dependencies(&clang, build, shown)? {
            found.extend(scan(path)?);
        }
    }

    let tmp = tempfile::tempdir().context("cannot create a temporary directory")?;
    let config_file = tmp.path().join("clang-tidy.yaml");
    fs::write(&config_file, config_text(&config))?;
    // Each build is its own run, decision 0047, and so is each entry of a compile database, decision 0048. The places that a run reports
    // judge only the findings of that run, because two builds can read one header with a marker in one and none in the other.
    // A run is `clang-tidy FILE -- FLAGS` from the directory of the build, so the flags of an entry read the paths that they were made for.
    for (n, (file, dir, flags)) in builds.iter().enumerate() {
        let fixes_file = tmp.path().join(format!("fixes-{n}.yaml"));
        let mut cmd = Command::new(&tool);
        cmd.current_dir(dir).args(load_arg(plugin));
        cmd.arg(format!("--config-file={}", config_file.display())).arg(format!("--export-fixes={}", fixes_file.display())).arg("--quiet");
        cmd.arg(file).arg("--").args(flags);
        let out = cmd.stdin(Stdio::null()).output().with_context(|| format!("cannot run {tool}"))?;
        // clang-tidy exits 1 whenever a finding exists, so only the fixes file tells. A clean run writes none.
        let fixes: Fixes = match fs::read_to_string(&fixes_file) {
            Ok(yaml) => parse(&yaml, "the clang-tidy fixes")?,
            Err(e) if e.kind() == ErrorKind::NotFound => Fixes::default(),
            Err(e) => return Err(e).context("cannot read the clang-tidy fixes"),
        };
        if !out.status.success() && fixes.diagnostics.is_empty() {
            bail!("clang-tidy failed ({}):\n{}", out.status, String::from_utf8_lossy(&out.stderr));
        }
        found.extend(judge(&loaded, fixes, &shown)?);
    }

    // The message is part of the key: a check in RULE_FIRST says something different about each construct on a line.
    found.sort_by(|a, b| (&a.path, a.line, &a.rule, &a.message).cmp(&(&b.path, b.line, &b.rule, &b.message)));
    found.dedup_by(|a, b| (&a.path, a.line, &a.rule, &a.message) == (&b.path, b.line, &b.rule, &b.message));

    for f in &found {
        if json {
            println!(
                r#"{{"rule":{},"check":{},"file":{},"line":{},"decision":"{}","message":{}}}"#,
                quote(&f.rule),
                quote(&f.check),
                quote(&shown(&f.path)),
                f.line,
                decision_word(f.decision),
                quote(&f.message)
            );
        } else {
            println!("Not provable: {}:{}: {}", shown(&f.path), f.line, f.message);
        }
    }
    if found.is_empty() && !json {
        println!("ok: no findings");
    }
    Ok(if found.is_empty() { ExitCode::SUCCESS } else { ExitCode::from(1) })
}

/// Run the tree check of the plugin alone and translate what it wrote. The working directory comes back with it, for the places.
fn read_model(plugin: Option<&Path>, file: &Path, clang_args: &[String]) -> Result<(model::Translation, PathBuf)> {
    // ponytail: the flags are judged without the rows of the policy, so a `-Wno-` flag of a warning that a row names passes here.
    // The model reads no warning. Upgrade: load the policy as the gate does.
    let refused = refused_flags(clang_args, &[]);
    if !refused.is_empty() {
        bail!("{}", refused.join("\n"));
    }
    let tool = locate(TIDY).context("clang-tidy not found. Install clang-tidy-18.")?;
    if !list_checks(&tool, plugin)?.iter().any(|l| l == TREE) {
        bail!("not enforced: no such check {TREE}. Build the plugin and pass --plugin PATH.");
    }
    let cwd = std::env::current_dir().context("cannot find the working directory")?;
    let tmp = tempfile::tempdir().context("cannot create a temporary directory")?;
    // The plugin appends, so the file starts empty, and a file with no function leaves it empty.
    let tree = tmp.path().join("tree.jsonl");
    fs::write(&tree, "")?;
    let config = tmp.path().join("clang-tidy.yaml");
    fs::write(&config, format!("Checks: \"-*,{TREE}\"\nCheckOptions:\n  {TREE}.Output: {}\n", quote(&tree.display().to_string())))?;
    let fixes_file = tmp.path().join("fixes.yaml");
    let run = Command::new(&tool)
        .current_dir(&cwd)
        .args(load_arg(plugin))
        .arg(format!("--config-file={}", config.display()))
        .arg(format!("--export-fixes={}", fixes_file.display()))
        .arg("--quiet")
        .arg(file)
        .arg("--")
        .args(clang_args)
        .stdin(Stdio::null())
        .output()
        .with_context(|| format!("cannot run {tool}"))?;
    // The check reports no finding, so what clang-tidy reports is the compiler's. The gate's own words, and exit 2.
    let fixes: Fixes = match fs::read_to_string(&fixes_file) {
        Ok(yaml) => parse(&yaml, "the clang-tidy fixes")?,
        Err(e) if e.kind() == ErrorKind::NotFound => Fixes::default(),
        Err(e) => return Err(e).context("cannot read the clang-tidy fixes"),
    };
    let shown = |p: &Path| p.strip_prefix(&cwd).unwrap_or(p).display().to_string();
    let broken: Vec<String> = fixes
        .diagnostics
        .iter()
        .filter(|d| d.name.starts_with(DIAGNOSTIC))
        .map(|d| does_not_compile(&Path::new(&d.dir).join(&d.at.file), d, &shown))
        .collect();
    if !broken.is_empty() {
        bail!("{}", broken.join("\n"));
    }
    if !run.status.success() {
        bail!("clang-tidy failed ({}):\n{}{}", run.status, String::from_utf8_lossy(&run.stdout), String::from_utf8_lossy(&run.stderr));
    }
    // The companion file of FILE.cpp is FILE.spec.dfy next to it, decision 0079.
    let spec = file.with_extension("spec.dfy");
    let companion = match fs::read_to_string(&spec) {
        Ok(text) => Some((spec.display().to_string(), text)),
        Err(e) if e.kind() == ErrorKind::NotFound => None,
        Err(e) => return Err(e).with_context(|| format!("cannot read {}", spec.display())),
    };
    let tree = fs::read_to_string(&tree).context("cannot read the tree")?;
    Ok((model::translate(&tree, companion.as_ref().map(|(p, t)| (p.as_str(), t.as_str())))?, cwd))
}

/// The path of a place, as the gate shows it: from the working directory.
fn shown_from(cwd: &Path, path: &str) -> String {
    let p = cwd.join(path);
    p.strip_prefix(cwd).unwrap_or(&p).display().to_string()
}

fn print_refusals(t: &model::Translation, cwd: &Path) {
    for (path, line, sentence) in &t.refusals {
        println!("Not provable: {}:{line}: {sentence}", shown_from(cwd, path));
    }
}

/// `cplusp model`: translate the functions of a file and write the Dafny file.
fn model(plugin: Option<&Path>, out: &Path, file: &Path, clang_args: &[String]) -> Result<ExitCode> {
    let (t, cwd) = read_model(plugin, file, clang_args)?;
    fs::write(out, &t.dafny).with_context(|| format!("cannot write {}", out.display()))?;
    print_refusals(&t, &cwd);
    Ok(if t.refusals.is_empty() { ExitCode::SUCCESS } else { ExitCode::from(1) })
}

/// `cplusp prove`: the gate first, as `cplusp gate` runs it, then the translator and the prover.
fn prove(common: &Common, plugin: Option<&Path>, time_limit: u32, file: &Path, clang_args: &[String]) -> Result<ExitCode> {
    // ponytail: the gate prints "ok: no findings" when it passes, and `prove` leaves it. Upgrade: a quiet flag on the gate.
    let code = gate(common, false, None, plugin, std::slice::from_ref(&file.to_path_buf()), clang_args)?;
    if code != ExitCode::SUCCESS {
        return Ok(code);
    }
    let (t, cwd) = read_model(plugin, file, clang_args)?;
    // Each trusted function of the model comes first, so the proof is read with the contracts it rests on, decisions 0102 and 0103.
    for (path, line, name, reason) in &t.trusted {
        println!("Trusted: {}:{line}: {name}: {reason}", shown_from(&cwd, path));
    }
    print_refusals(&t, &cwd);
    prove::run(&t, time_limit, !t.refusals.is_empty(), &shown_from(&cwd, &file.display().to_string()), &|path| shown_from(&cwd, path))
}

/// The line the gate prints for a compiler error. The model prints the same.
fn does_not_compile(path: &Path, d: &Diagnostic, shown: &dyn Fn(&Path) -> String) -> String {
    // An empty file name means clang had no input file at all. A pseudo-file such as
    // `<command line>` cannot be read back, so the line is left out rather than lost.
    let place = match (d.at.file.is_empty(), line_of(path, d.at.offset)) {
        (true, _) => String::new(),
        (false, Ok(line)) => format!("{}:{line}: ", shown(path)),
        (false, Err(_)) => format!("{}: ", shown(path)),
    };
    format!("does not compile: {place}{}", d.at.message)
}

/// The findings of one run of clang-tidy. `fixes` is what the run reported. The places of the run decide the kind of each of its findings.
fn judge(loaded: &Loaded, fixes: Fixes, shown: &dyn Fn(&Path) -> String) -> Result<Vec<Finding>> {
    let mut found = Vec::new();
    let mut seen = HashSet::new();
    let diagnostics: Vec<_> = fixes
        .diagnostics
        .into_iter()
        .map(|d| (Path::new(&d.dir).join(&d.at.file), d))
        // The message is part of the key: the generic check reports two rules at one place with one name.
        .filter(|(path, d)| seen.insert((d.name.clone(), path.clone(), d.at.offset, d.at.message.clone())))
        .collect();

    // A check that reports a bad option means the policy gave the plugin something it cannot use.
    let bad: Vec<&str> = diagnostics.iter().filter(|(_, d)| d.name == CONFIG_ERROR).map(|(_, d)| d.at.message.as_str()).collect();
    if !bad.is_empty() {
        bail!("{}", bad.join("\n"));
    }

    // A source that does not compile cannot be judged, so this comes before any finding.
    // With `-*` every compiler warning outside the policy is off, so one that is left is an error.
    let mut broken = Vec::new();
    for (path, d) in &diagnostics {
        if d.name.starts_with(DIAGNOSTIC) && rule_for_check(&loaded.policy, &d.name).is_none() {
            broken.push(does_not_compile(path, d, shown));
        }
    }
    if !broken.is_empty() {
        bail!("{}", broken.join("\n"));
    }

    // The functions of each file, from the regions the plugin reports for this run. A finding takes the kind of the innermost one that
    // holds it, and the core says which that is.
    let mut regions: BTreeMap<PathBuf, Vec<Region>> = BTreeMap::new();
    for (path, d) in diagnostics.iter().filter(|(_, d)| d.name == MARKERS) {
        if let Some(region) = region(&d.at) {
            regions.entry(path.clone()).or_default().push(region);
        }
    }
    let nowhere = Vec::new();

    for (path, d) in diagnostics {
        if d.name == PRAGMA {
            let (file, line, message) = presumed(&d)?;
            let rule = if message.starts_with("include:") { "include" } else { "pragma" };
            found.push(ban(file, line, rule, message));
            continue;
        }
        // A marker finding stands in every kind of function. A region is no finding. A call that reaches plain code and a use of a plain
        // type are findings in a verified place only: a trusted body may run plain code, and a plain function runs it and uses it.
        if d.name == MARKERS {
            let sentence = named(&d.at, "reach ")
                .map(|name| format!("calls {name}, which is plain. Give it a contract and mark it trusted."))
                .or_else(|| named(&d.at, "uses ").map(|name| format!("uses {name}, which is plain. Reach it through a trusted member.")));
            if let Some(sentence) = sentence {
                if kind_at(regions.get(&path).unwrap_or(&nowhere), d.at.offset as u64) == Kind::Verified {
                    found.push(ban(path.clone(), line_of(&path, d.at.offset)?, "marker", &format!("marker: verified code {sentence}")));
                }
            } else if region(&d.at).is_none() {
                let (file, line, message) = presumed(&d)?;
                found.push(ban(file, line, "marker", message));
            }
            continue;
        }
        if d.name == LINE_DIRECTIVE {
            let message = "line directive: not allowed in verified code. It moves the gate's view.";
            found.push(ban(path.clone(), line_of(&path, d.at.offset)?, "line", message));
            continue;
        }
        // A check in RULE_FIRST puts the rule id first in the message, and may follow it with a sentence for the bot.
        // Every other check maps by its name.
        let rule_first = RULE_FIRST.contains(&d.name.as_str());
        let (id, sentence) = d.at.message.split_once(": ").unwrap_or((&d.at.message, ""));
        let i = if rule_first {
            match rule_by_id(&loaded.policy, &id.to_string()) {
                Some(i) if is_active(&loaded.policy.rules[i]) => Some(i),
                // A team loosened the row, and the kinds it claims are loosened with it.
                Some(_) if d.name == ALLOWLIST => continue,
                _ => bail!("{} reported {}, which is not a rule the gate enforces", d.name, d.at.message),
            }
        } else {
            rule_for_check(&loaded.policy, &d.name)
        };
        let Some(i) = i else { continue };
        let (rule, doc) = (&loaded.policy.rules[i], &loaded.docs[i]);
        // The kind of the function that holds the finding decides, and the core says whether the finding stands there.
        if !keep_finding(rule.decision, kind_at(regions.get(&path).unwrap_or(&nowhere), d.at.offset as u64)) {
            continue;
        }
        // The core promises a limit and a use_instead on every rule it maps a finding to.
        let (limit, instead) = (rule.limit.as_deref().unwrap_or(""), rule.use_instead.as_deref().unwrap_or(""));
        let mut message = match rule.decision {
            Decision::Ban => format!("{}: not allowed in verified code. {} Use {instead}", doc.construct, rule.why),
            Decision::TrustedOnly => format!("{}: allowed only in trusted code. {} Use {instead}", doc.construct, rule.why),
            // `rule_for_check` never returns an allow rule.
            Decision::Restrict | Decision::Allow => format!("{}: outside its limit. Limit: {limit} Use {instead}", doc.construct),
        };
        if rule_first && !sentence.is_empty() {
            message = format!("{message} {sentence}");
        }
        let line = line_of(&path, d.at.offset)?;
        found.push(Finding { path, line, rule: rule.id.clone(), check: d.name, decision: rule.decision, message });
    }
    Ok(found)
}

/// The place and the sentence of a finding of the gate's own. The message of the plugin is the presumed file, the presumed line and the
/// sentence, set apart by tabs. A `#line` moves the presumed place, and a finding shows the place that the author gave. The sentence
/// holds no tab and the line is digits. The file name may hold a tab, so the message is cut from the right.
fn presumed(d: &Diagnostic) -> Result<(PathBuf, usize, &str)> {
    let mut parts = d.at.message.rsplitn(3, '\t');
    let (Some(message), Some(line), Some(file)) = (parts.next(), parts.next().and_then(|n| n.parse().ok()), parts.next()) else {
        bail!("{} reported {}, which is not a finding of that check", d.name, d.at.message);
    };
    Ok((Path::new(&d.dir).join(file), line, message))
}

/// The region that a report of `cplusp-markers` gives: `region {verified|trusted|plain} {end}`, at the first byte of the region.
/// A finding of the check starts with a file name and has tabs, so it does not parse as a region.
fn region(at: &At) -> Option<Region> {
    let (kind, end) = at.message.strip_prefix("region ")?.split_once(' ')?;
    let kind = match kind {
        "verified" => Kind::Verified,
        "trusted" => Kind::Trusted,
        "plain" => Kind::Plain,
        _ => return None,
    };
    Some(Region { begin: at.offset as u64, end: end.parse().ok()?, kind })
}

/// The name in a report of `cplusp-markers` of the form `reach {qualified name}`, at a call that runs a plain function, or of the form
/// `uses {qualified name}`, at a use of a plain type. The name runs to the end and can hold a space, as in `operator int`. A finding of the
/// check has tabs, so it is none.
fn named<'a>(at: &'a At, form: &str) -> Option<&'a str> {
    at.message.strip_prefix(form).filter(|name| !name.contains('\t'))
}

// ponytail: reads the whole file to turn a byte offset into a line, once per diagnostic.
// An offset past the end clamps to the last line, which only a file changed during the run can reach.
// Upgrade: read each file once, and fail on an offset past the end.
fn line_of(path: &Path, offset: usize) -> Result<usize> {
    let source = fs::read(path).with_context(|| format!("cannot read {}", path.display()))?;
    // A line ends as the compiler counts it: with `\n`, with `\r\n`, or with a bare `\r`.
    let breaks = source[..offset.min(source.len())]
        .iter()
        .enumerate()
        .filter(|&(i, &b)| b == b'\n' || (b == b'\r' && source.get(i + 1) != Some(&b'\n')))
        .count();
    Ok(1 + breaks)
}

/// A JSON string.
fn quote(s: &str) -> String {
    let mut out = String::from("\"");
    for c in s.chars() {
        match c {
            '"' => out += "\\\"",
            '\\' => out += "\\\\",
            '\n' => out += "\\n",
            c if c < ' ' => out += &format!("\\u{:04x}", c as u32),
            c => out.push(c),
        }
    }
    out + "\""
}
