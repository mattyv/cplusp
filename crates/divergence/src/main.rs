//! `cargo run -p divergence > docs/mitigations.md`, from the repository root.

fn main() -> Result<(), Box<dyn std::error::Error>> {
    print!("{}", divergence::report(std::path::Path::new("divergence/cases"))?);
    Ok(())
}
