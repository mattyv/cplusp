// Model B: the init value is int64_t{0}, so the accumulator is an int64 and Dafny checks every step of the fold.
// The bounds keep every partial sum in int64: every element fits int32, and there are fewer than 2^31 of them.
newtype int32 = x: int | -0x8000_0000 <= x < 0x8000_0000
newtype int64 = x: int | -0x8000_0000_0000_0000 <= x < 0x8000_0000_0000_0000

function Sum(s: seq<int64>): int
  decreases |s|
{
  if |s| == 0 then 0 else Sum(s[..|s| - 1]) + (s[|s| - 1] as int)
}

method total(v: seq<int64>) returns (result: int64)
  requires |v| < 0x8000_0000
  requires forall i :: 0 <= i < |v| ==> -0x8000_0000 <= v[i] < 0x8000_0000
  ensures result as int == Sum(v)
{
  var acc: int64 := 0;
  for i := 0 to |v|
    invariant -0x8000_0000 * i <= acc as int <= 0x7FFF_FFFF * i
    invariant acc as int == Sum(v[..i])
  {
    assert v[..i + 1] == v[..i] + [v[i]];
    acc := acc + v[i];
  }
  assert v[..|v|] == v;
  result := acc;
}
