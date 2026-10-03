// Model A: the fold is a sum over the seq in unbounded int, and the result is the exact sum.
// Dafny proves it. The C++ runs the fold in int, so the model does not describe it.
// The bound on the whole sum keeps the result in int64, which the contract needs.
newtype int64 = x: int | -0x8000_0000_0000_0000 <= x < 0x8000_0000_0000_0000

function Sum(s: seq<int64>): int
  decreases |s|
{
  if |s| == 0 then 0 else Sum(s[..|s| - 1]) + (s[|s| - 1] as int)
}

method total(v: seq<int64>) returns (result: int64)
  requires -0x8000_0000_0000_0000 <= Sum(v) < 0x8000_0000_0000_0000
  ensures result as int == Sum(v)
{
  var acc: int := 0;
  for i := 0 to |v|
    invariant acc == Sum(v[..i])
  {
    assert v[..i + 1] == v[..i] + [v[i]];
    acc := acc + (v[i] as int);
  }
  assert v[..|v|] == v;
  result := acc as int64;
}
