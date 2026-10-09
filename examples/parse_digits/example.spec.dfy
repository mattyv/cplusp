// Value is the number that the digits spell, and the lemmas of example.dfy bound it. A digit is a byte from 48, the code of '0',
// to 57, the code of '9'.
function Value(s: seq<uint8>): int
  decreases |s|
{
  if |s| == 0 then 0 else 10 * Value(s[..|s| - 1]) + (s[|s| - 1] as int - 48)
}

function Pow10(n: nat): nat
  decreases n
  ensures Pow10(n) >= 1
{
  if n == 0 then 1 else 10 * Pow10(n - 1)
}

predicate IsDigit(b: uint8) {
  48 <= b as int <= 57
}

lemma ValueBound(s: seq<uint8>)
  requires forall j :: 0 <= j < |s| ==> IsDigit(s[j])
  ensures 0 <= Value(s) < Pow10(|s|)
  decreases |s|
{
  if |s| > 0 {
    ValueBound(s[..|s| - 1]);
  }
}

lemma Pow10AtMost(i: nat, j: nat)
  requires i <= j
  ensures Pow10(i) <= Pow10(j)
  decreases j
{
  if i < j {
    Pow10AtMost(i, j - 1);
  }
}
