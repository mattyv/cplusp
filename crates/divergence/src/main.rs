//! `cargo run -p divergence -- dafny > docs/mitigations-dafny.md`, from the repository root.

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let args: Vec<String> = std::env::args().collect();
    let [_, prover] = args.as_slice() else {
        eprintln!("usage: divergence <prover>");
        std::process::exit(2);
    };
    print!("{}", divergence::report(&std::path::Path::new("divergence").join(prover))?);
    Ok(())
}
