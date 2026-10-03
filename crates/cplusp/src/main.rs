//! The `cplusp` command line. It parses files, runs clang-tidy and prints text.
//! Every policy decision comes from `cplusp_core`. See docs/policy.md.

use std::collections::{BTreeMap, HashSet};
use std::fs;
use std::io::ErrorKind;
use std::path::{Path, PathBuf};
use std::process::{Command, ExitCode, Stdio};

use anyhow::{anyhow, bail, Context, Result};
use clap::{Args, Parser, Subcommand};
use cplusp_core::{
    apply_overrides, emit, is_active, keep_finding, rule_by_id, rule_for_check, validate, CheckOption, CheckRef, Config, Decision,
    Kind, Override, Policy, PolicyError, Rule,
};
use serde::de::{DeserializeOwned, IgnoredAny};
use serde::Deserialize;

/// The default policy lives in the binary, so `extends` works from any directory.
const DEFAULT_POLICY: &str = include_str!("../../../policy/cplusp-policy.yaml");

/// Compiler diagnostics are not in `clang-tidy --list-checks`. Their names start like this.
const DIAGNOSTIC: &str = "clang-diagnostic-";

/// What clang-tidy names the diagnostic of a check that is given a bad option.
const CONFIG_ERROR: &str = "clang-tidy-config";

/// The generic check of the plugin. A `matcher` entry of the policy becomes an option of this check.
const MATCHER: &str = "cplusp-matcher";

/// Checks that the clang-tidy plugin will add. The policy may name them today.
// ponytail: a hand-kept list. Upgrade: load the plugin and read its `--list-checks`.
const PLANNED_CHECKS: &[&str] = &[
    MATCHER, "cplusp-mutable", "cplusp-multiple-inheritance", "cplusp-iterator-arithmetic", "cplusp-impure-operator",
    "cplusp-recursion", "cplusp-lambda-limits", "cplusp-unlisted-state",
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
            let listed = locate().map(|tool| list_checks(&tool, None)).transpose()?;
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

/// Flags that change floating-point results. The float model is a real after one IEEE 754 rounding.
const FLOAT_FLAGS: &[&str] = &[
    "-ffast-math", "-Ofast", "-funsafe-math-optimizations", "-ffinite-math-only", "-fassociative-math",
    "-freciprocal-math", "-fno-signed-zeros", "-fno-honor-nans", "-fno-honor-infinities", "-ffp-model=fast", "-mfpmath=387", "-m32",
];

/// The `-std` values at C++23 or later. The baseline is decision 0022.
const STD_VALUES: &[&str] = &["c++23", "c++2b", "c++26", "c++2c", "gnu++23", "gnu++2b", "gnu++26", "gnu++2c"];

/// What a flag sets contraction to. `-ffp-model=precise` is `on` and `-ffp-model=strict` is `off`.
fn contraction(f: &str) -> Option<&str> {
    match f {
        "-ffp-model=precise" => Some("on"),
        "-ffp-model=strict" => Some("off"),
        _ => f.strip_prefix("-ffp-contract="),
    }
}

/// The value of `-std=X`. `--std=X` is the same flag.
fn std_value(f: &str) -> Option<&str> {
    f.strip_prefix("-std=").or_else(|| f.strip_prefix("--std="))
}

/// One message for each trailing flag the proofs cannot follow, and for each flag the gate needs and does not find.
/// `checks` is the check list of the generated config, so a `-Wno-{name}` is judged against the rows the policy enables.
// ponytail: the flags are matched as written. A flag behind `-Xclang` or in a response file passes.
// Upgrade: ask the compiler for its final flags.
fn refused_flags(flags: &[String], checks: &[String]) -> Vec<String> {
    let mut refused = Vec::new();
    // The last flag that sets contraction is the one the compiler follows.
    let last_contract = flags.iter().rposition(|f| contraction(f).is_some());
    for (i, f) in flags.iter().enumerate() {
        let contracts = Some(i) == last_contract && contraction(f) != Some("off");
        let denormals = f.starts_with("-fdenormal-fp-math=") && f != "-fdenormal-fp-math=ieee";
        let why = if contracts || denormals || FLOAT_FLAGS.contains(&f.as_str()) {
            "It changes floating-point results, and the proofs assume IEEE 754 round to nearest."
        } else if std_value(f).is_some_and(|v| !STD_VALUES.contains(&v)) {
            "The proofs assume C++23 or later."
        } else if f == "-w" || f == "-Wno-everything" {
            "It hides the compiler warnings the policy names."
        } else if f.strip_prefix("-Wno-").is_some_and(|n| checks.iter().any(|c| c.strip_prefix(DIAGNOSTIC) == Some(n))) {
            "It hides a compiler warning the policy names."
        } else {
            continue;
        };
        refused.push(format!("{f}: not allowed with the gate. {why}"));
    }
    if !flags.iter().any(|f| std_value(f).is_some()) {
        refused.push("no -std flag: the gate needs -std=c++23 or later, because the proofs assume C++23.".to_string());
    }
    if !flags.iter().any(|f| contraction(f) == Some("off")) {
        refused.push("no -ffp-contract=off: the gate needs it, because the proofs assume no fused multiply-add.".to_string());
    }
    refused
}

// --------------------------------------------------------------------- clang-tidy

/// `clang-tidy-18`, else `clang-tidy`, whichever runs.
fn locate() -> Option<String> {
    let runs = |bin: &str| Command::new(bin).arg("--version").output().is_ok_and(|o| o.status.success());
    ["clang-tidy-18", "clang-tidy"].into_iter().find(|b| runs(b)).map(String::from)
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

/// One thing the gate reports. `rule` and `check` are `nolint` for a suppression.
struct Finding {
    path: PathBuf,
    line: usize,
    rule: String,
    check: String,
    decision: Decision,
    message: String,
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
    let tool = locate().context("clang-tidy not found. Install clang-tidy-18.")?;
    let listed = list_checks(&tool, plugin)?;
    // clang-tidy ignores a plugin it cannot load, and then every `cplusp-matcher` rule goes quiet.
    if let Some(p) = plugin.filter(|_| !listed.iter().any(|l| l == MATCHER)) {
        bail!("plugin {} did not load. It must provide {MATCHER}.", p.display());
    }
    let loaded = load(c.policy.as_deref(), Some(&listed))?;
    let config = emit(&loaded.policy);
    // ponytail: with `-p` the flags come from the database, and the gate does not read them.
    // Upgrade: read `compile_commands.json` and run `refused_flags` over each command.
    if build_dir.is_none() {
        let refused = refused_flags(clang_args, &config.checks);
        if !refused.is_empty() {
            bail!("{}", refused.join("\n"));
        }
    }
    let missing: Vec<&str> =
        config.checks.iter().map(String::as_str).filter(|k| !k.starts_with(DIAGNOSTIC) && !listed.iter().any(|l| l == k)).collect();
    if !missing.is_empty() {
        eprintln!("warning: not enforced, no such check: {}", missing.join(", "));
    }

    // A NOLINT silences clang-tidy, so it would hide a finding from the gate. It is a finding itself.
    // ponytail: only the passed files are scanned. Headers wait for the plugin, which sees every suppression.
    let cwd = std::env::current_dir().context("cannot find the working directory")?;
    let mut found = Vec::new();
    for file in files {
        let source = fs::read(file).with_context(|| format!("cannot read {}", file.display()))?;
        for (n, _) in String::from_utf8_lossy(&source).lines().enumerate().filter(|(_, l)| l.contains("NOLINT")) {
            found.push(Finding {
                path: cwd.join(file),
                line: n + 1,
                rule: "nolint".to_string(),
                check: "nolint".to_string(),
                decision: Decision::Ban,
                message: "NOLINT: not allowed in verified code. It silences the gate. Use CPLUSP_TRUSTED with a reason.".to_string(),
            });
        }
    }

    let tmp = tempfile::tempdir().context("cannot create a temporary directory")?;
    let (config_file, fixes_file) = (tmp.path().join("clang-tidy.yaml"), tmp.path().join("fixes.yaml"));
    fs::write(&config_file, config_text(&config))?;
    let mut cmd = Command::new(&tool);
    cmd.args(load_arg(plugin));
    cmd.arg(format!("--config-file={}", config_file.display())).arg(format!("--export-fixes={}", fixes_file.display())).arg("--quiet");
    if let Some(d) = build_dir {
        cmd.arg("-p").arg(d);
    }
    cmd.args(files);
    if !clang_args.is_empty() {
        cmd.arg("--").args(clang_args);
    }
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

    let shown = |p: &Path| p.strip_prefix(&cwd).unwrap_or(p).display().to_string();
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
            // An empty file name means clang had no input file at all. A pseudo-file such as
            // `<command line>` cannot be read back, so the line is left out rather than lost.
            let place = match (d.at.file.is_empty(), line_of(path, d.at.offset)) {
                (true, _) => String::new(),
                (false, Ok(line)) => format!("{}:{line}: ", shown(path)),
                (false, Err(_)) => format!("{}: ", shown(path)),
            };
            broken.push(format!("does not compile: {place}{}", d.at.message));
        }
    }
    if !broken.is_empty() {
        bail!("{}", broken.join("\n"));
    }

    for (path, d) in diagnostics {
        // The generic check puts the rule id in the message. Every other check maps by its name.
        let i = if d.name == MATCHER {
            match rule_by_id(&loaded.policy, &d.at.message) {
                Some(i) if is_active(&loaded.policy.rules[i]) => Some(i),
                _ => bail!("{MATCHER} reported {}, which is not a rule the gate enforces", d.at.message),
            }
        } else {
            rule_for_check(&loaded.policy, &d.name)
        };
        let Some(i) = i else { continue };
        let (rule, doc) = (&loaded.policy.rules[i], &loaded.docs[i]);
        // ponytail: every finding counts as inside a verified function until the clang-tidy plugin
        // reports function kinds. Upgrade: read the kind from the plugin's `cplusp-markers` output.
        if !keep_finding(rule.decision, Kind::Verified) {
            continue;
        }
        // The core promises a limit and a use_instead on every rule it maps a finding to.
        let (limit, instead) = (rule.limit.as_deref().unwrap_or(""), rule.use_instead.as_deref().unwrap_or(""));
        let message = match rule.decision {
            Decision::Ban => format!("{}: not allowed in verified code. {} Use {instead}", doc.construct, rule.why),
            Decision::TrustedOnly => format!("{}: allowed only in trusted code. {} Use {instead}", doc.construct, rule.why),
            // `rule_for_check` never returns an allow rule.
            Decision::Restrict | Decision::Allow => format!("{}: outside its limit. Limit: {limit} Use {instead}", doc.construct),
        };
        let line = line_of(&path, d.at.offset)?;
        found.push(Finding { path, line, rule: rule.id.clone(), check: d.name, decision: rule.decision, message });
    }
    found.sort_by(|a, b| (&a.path, a.line, &a.rule).cmp(&(&b.path, b.line, &b.rule)));
    found.dedup_by(|a, b| (&a.path, a.line, &a.rule) == (&b.path, b.line, &b.rule));

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

// ponytail: reads the whole file to turn a byte offset into a line, once per diagnostic.
// An offset past the end clamps to the last line, which only a file changed during the run can reach.
// Upgrade: read each file once, and fail on an offset past the end.
fn line_of(path: &Path, offset: usize) -> Result<usize> {
    let source = fs::read(path).with_context(|| format!("cannot read {}", path.display()))?;
    Ok(1 + source[..offset.min(source.len())].iter().filter(|&&b| b == b'\n').count())
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
