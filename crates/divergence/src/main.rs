//! `cargo run -p divergence -- dafny > docs/mitigations-dafny.md`, from the repository root.
//! `cargo run -p divergence -- differential divergence/dafny/cases/CASE [--naive]` is the differential run of decision 0034.

use divergence::Outcome;

/// The exit code is 0 for agree, 1 for diverge and 2 for a run that could not complete.
fn differential(dir: &str, naive: bool) -> ! {
    match divergence::differential(dir.as_ref(), naive) {
        Ok(Outcome::Agree(line)) => println!("{line}"),
        Ok(Outcome::Diverge(line)) => {
            println!("{line}");
            std::process::exit(1);
        }
        Err(e) => {
            eprintln!("{e}");
            std::process::exit(2);
        }
    }
    std::process::exit(0)
}

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let args: Vec<String> = std::env::args().collect();
    match args.iter().map(String::as_str).collect::<Vec<_>>().as_slice() {
        [_, "differential", dir] => differential(dir, false),
        [_, "differential", dir, "--naive"] => differential(dir, true),
        // A `differential` it did not understand is a usage error, never a prover of that name.
        [_, prover] if *prover != "differential" => print!("{}", divergence::report(&std::path::Path::new("divergence").join(prover))?),
        _ => {
            eprintln!("usage: divergence <prover> | divergence differential CASE_DIR [--naive]");
            std::process::exit(2);
        }
    }
    Ok(())
}
