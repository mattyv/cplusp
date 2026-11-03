# Use cplusp

This guide builds cplusp, proves a small function, and shows a failed proof.
Run the commands from the repository root. To change the tool itself, continue
with [Contribute to cplusp](contributing.md).

## Build

The CI environment is Ubuntu 24.04 on x86-64. Other platforms need their own
toolchain setup. These commands follow the repository's
[CI configuration](../.github/workflows/check.yml).

You need Git and Rust's `rustup` command before starting. Clone the repository
if you do not already have a checkout:

```sh
git clone https://github.com/mattyv/cplusp.git
cd cplusp
```

Install the C++ build tools and the Rust version pinned in
[rust-toolchain.toml](../rust-toolchain.toml):

```sh
sudo apt-get update
sudo apt-get install -y clang-18 clang-tidy-18 libclang-18-dev llvm-18-dev \
  libclang-rt-18-dev g++ cmake ninja-build curl unzip
rustup toolchain install 1.98.1 --profile minimal
cmake -S clang-tidy -B target/plugin -G Ninja
cmake --build target/plugin
cargo build --locked -p cplusp
```

These commands produce `target/debug/cplusp` and `target/plugin/libcplusp.so`.
They do not install a `cplusp` command on your `PATH`.

Install the Dafny release used by CI. The checksum below is the one recorded in
the workflow:

```sh
mkdir -p target/dafny
curl --fail --location --retry 3 \
  https://github.com/dafny-lang/dafny/releases/download/v4.11.0/dafny-4.11.0-x64-ubuntu-22.04.zip \
  --output target/dafny.zip
echo 'a46a9ff7cdd720f7955854c78e95df13f4cfe6b80691b05f8654fe19e8267179  target/dafny.zip' | sha256sum --check
unzip -q -o target/dafny.zip -d target/dafny
export DAFNY="$PWD/target/dafny/dafny/dafny"
"$DAFNY" --version
```

Keep `DAFNY` set in each shell where you run proofs. The CLI uses that executable
when the variable is nonempty. An invalid path stops the run.
Verifying cplusp's own Rust core requires a separate Verus setup, described in
the [contributor guide](contributing.md#verify-the-core).

## Run a passing proof

Open [model-clamp.cpp](../crates/cplusp/tests/fixtures/model-clamp.cpp).
The function returns `lo` below the range, `hi` above it, and `x` inside it.
Its contract states those cases:

```cpp
//@ requires lo <= hi
//@ ensures lo <= result && result <= hi
//@ ensures x < lo ==> result == lo
//@ ensures x > hi ==> result == hi
//@ ensures lo <= x && x <= hi ==> result == x
```

`requires` states what a caller must establish. `ensures` states what the
function promises on return. `result` names the return value. `==>` means
implication: if the left side holds, the right side must hold.

Integer arithmetic in contracts uses exact integers. The translated C++ body
still carries machine-type range checks. See [contract semantics](soundness.md#gap-4-the-contract-language).

```sh
./target/debug/cplusp prove --plugin target/plugin/libcplusp.so \
  crates/cplusp/tests/fixtures/model-clamp.cpp -- -std=c++23 -ffp-contract=off
```

With the configured toolchain, this regression fixture should exit 0 and end with:

```text
ok: proved
```

The run also prints `ok: no findings` after the gate passes. That earlier line
alone is not a proof result.

## Run a failing proof

[model-clamp-wrong.cpp](../crates/cplusp/tests/fixtures/model-clamp-wrong.cpp)
has a contract that promises `hi` when `x < lo`. Its body returns `lo`.
Run it with the same settings:

```sh
./target/debug/cplusp prove --plugin target/plugin/libcplusp.so \
  crates/cplusp/tests/fixtures/model-clamp-wrong.cpp -- -std=c++23 -ffp-contract=off
```

This fixture should exit 1. The diagnostic includes:

```text
Not proved: crates/cplusp/tests/fixtures/model-clamp-wrong.cpp:8: the ensures line may not hold on this return.
```

The following lines identify the contract and its assumptions. A failure can
expose wrong code, a wrong contract, or a missing proof argument. Check the
requirement before changing either the code or the contract.

## Check your own code

Start with one function and an example that uses similar types. Use fixed-width
integers such as `int32_t` from `<cstdint>`. Put the contract immediately above
the function. Run `prove` with the include paths and definitions your build uses:

```sh
./target/debug/cplusp prove --plugin target/plugin/libcplusp.so \
  path/to/file.cpp -- -std=c++23 -ffp-contract=off -Ipath/to/include
```

The paths above are placeholders. Keep both required build flags. The gate
refuses settings that conflict with its assumptions, including fast math.
The target and floating-point assumptions are listed in [soundness](soundness.md).

Functions are verified by default. The markers in
[include/cplusp.h](../include/cplusp.h) change how the tool treats them:

| Kind | Meaning |
| --- | --- |
| Verified | Check the body against its contract and the model's safety obligations. |
| `CPLUSP_TRUSTED("reason")` | Use the contract without proving the body. Some gate restrictions still apply. |
| `CPLUSP_PLAIN("reason")` | Exclude the function from verification. Verified code cannot call it directly. |

Review every trusted contract. It can make a caller's proof pass even when the
trusted implementation is wrong. Code outside verification must also satisfy
the preconditions of any verified function it calls.

More complex contracts can use a companion file. For `file.cpp`, place Dafny
specification functions and lemmas in `file.spec.dfy` beside it. See the
[contract guide](../skills/cplusp-dafny/SKILL.md) for the accepted forms and restrictions.
The compiler ignores `//@` comments. They do not add runtime checks.

## Choose a command

| Command | Purpose | Success means |
| --- | --- | --- |
| `gate --plugin PATH FILE… -- FLAGS…` | Check the policy. | No gate finding remained. |
| `model --plugin PATH --out FILE.dfy FILE.cpp -- FLAGS…` | Inspect the translation. | The translator refused no construct. No proof ran. |
| `prove --plugin PATH FILE.cpp -- FLAGS…` | Run the complete check. | The generated model proved under its assumptions. |
| `policy show` | Read the active rules. | The policy loaded. |
| `policy check` | Validate policy data and known check names. | The policy passed validation. No C++ was checked. |

Use `./target/debug/cplusp --help` or a subcommand's `--help` for its options.
`gate` and `prove` accept `--policy FILE`. `prove --time-limit 60` changes the
per-method limit from 20 seconds to 60. Zero is refused.

Only `gate` accepts a compilation database:

```sh
./target/debug/cplusp gate --plugin target/plugin/libcplusp.so \
  -p path/to/build path/to/file.cpp
```

The build directory must contain `compile_commands.json`. Use its `arguments`
form when a command needs quoting. Use either `-p` or trailing `--` flags.
For `prove`, supply the relevant compile flags explicitly.

## Read the result

The gate groups repeated findings with the same rule and message. It shows
up to three locations for each group and counts any remaining locations.
This also applies to the gate inside `prove`. Run `cplusp gate --json` with
the same inputs and build settings to see every finding and its full message.

For `prove`, exit 0 means success, exit 1 means the file was refused or did not
prove, and exit 2 means the run could not produce a valid result.

| Output | Next step |
| --- | --- |
| `Not provable:` | Read the named policy or translation limit. Use a supported form. |
| `Not proved:` | Inspect the obligation, contract and assumptions. A timeout also leaves the result unknown. |
| `Trusted:` or `Axiom:` | Review the assumption. These lines can appear in a successful run. |
| `does not compile:` | Fix the C++ error or supply the missing build flags. |
| `not enforced: no such check` | Build the plugin and pass its path with `--plugin`. |
| `DAFNY names … and it does not run` | Correct or unset `DAFNY`. Check the executable with `--version`. |

A gate pass can still be followed by a translation refusal. Policy support and
translation support are separate. A model file can also exist after a refusal.
Check the exit status before using its contents.

## What to retain with a result

Keep the source revision, command, build flags, policy, tool versions and full
output. Review the preconditions and trusted dependencies. Recheck affected
callers when their contracts change. The CLI does not track those callers for you.

Read the [proof FAQ](formal-proof-faq.md) for examples of weak contracts and
vacuous proofs. Read [soundness](soundness.md) for the project's known gaps.
