use super::*;

// A child process keeps tool discovery isolated from tests running in parallel.
fn without_tools(test: &str, dafny: &Path) -> String {
    let empty = tempfile::tempdir().unwrap();
    let output = Command::new(std::env::current_exe().unwrap())
        .args(["--exact", test, "--nocapture"])
        .env("PATH", empty.path())
        .env("DAFNY", dafny)
        .current_dir(root())
        .output()
        .unwrap();
    let text = format!("{}{}", stdout(&output), stderr(&output));
    assert!(!output.status.success(), "a test without its required tool must fail: {text}");
    text
}

#[test]
fn missing_clang_tidy_fails_the_test() {
    let text = without_tools("gate::gate_passes_an_allowed_sample_and_fails_a_banned_one", Path::new("missing-dafny"));
    assert!(text.contains("clang-tidy is required"), "{text}");
}

#[test]
fn missing_dafny_fails_the_test() {
    let empty = tempfile::tempdir().unwrap();
    let text = without_tools("basics::the_model_of_clamp_verifies_in_dafny", &empty.path().join("dafny"));
    assert!(text.contains("Dafny is required"), "{text}");
}

#[test]
fn a_dafny_that_cannot_start_fails_the_test() {
    let empty = tempfile::tempdir().unwrap();
    let broken = empty.path().join("dafny");
    std::fs::write(&broken, "not an executable").unwrap();
    let text = without_tools("basics::the_model_of_clamp_verifies_in_dafny", &broken);
    assert!(text.contains("Dafny is required"), "{text}");
}
