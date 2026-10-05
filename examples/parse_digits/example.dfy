// A span of bytes is a seq<uint8>, and the optional is a datatype. Value is the specification the contract names, and IsDigit is
// the test `'0' <= b <= '9'`. A digit string of nine digits or fewer is below 10^9, and the lemmas show it. The value of the digits
// read so far is below 10 to the power of their count. That power is at most 10^8 before the ninth digit, so `acc * 10 + digit`
// stays inside int32.
newtype int32 = x: int | -0x8000_0000 <= x < 0x8000_0000
newtype uint8 = x: int | 0 <= x < 0x100
newtype uint64 = x: int | 0 <= x < 0x1_0000_0000_0000_0000

datatype Option<T> = None | Some(value: T)

function Value(s: seq<uint8>): int
  decreases |s|
{
  if |s| == 0 then 0 else 10 * Value(s[..|s| - 1]) + (s[|s| - 1] as int - '0' as int)
}

function Pow10(n: nat): nat
  decreases n
  ensures Pow10(n) >= 1
{
  if n == 0 then 1 else 10 * Pow10(n - 1)
}

predicate IsDigit(b: uint8) {
  '0' as int <= b as int <= '9' as int
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

method parse_digits(digits: seq<uint8>) returns (result: Option<int32>)
  requires |digits| <= 9
  ensures result.Some? <==> (|digits| > 0 && forall i :: 0 <= i < |digits| ==> IsDigit(digits[i]))
  ensures result.Some? ==> result.value as int == Value(digits)
{
  if |digits| == 0 {
    return None;
  }
  var acc: int32 := 0;
  var i: uint64 := 0;
  while i as int < |digits|
    invariant i as int <= |digits|
    invariant forall j :: 0 <= j < i as int ==> IsDigit(digits[j])
    invariant acc as int == Value(digits[..i])
    decreases |digits| - i as int
  {
    var d := digits[i];
    if !IsDigit(d) {
      return None;
    }
    ValueBound(digits[..i]);
    Pow10AtMost(i as int, 8);
    assert Pow10(8) == 100_000_000;
    assert digits[..i + 1][..i] == digits[..i];
    acc := acc * 10 + (d as int32 - '0' as int32);
    i := i + 1;
  }
  assert digits[..i] == digits;
  return Some(acc);
}
