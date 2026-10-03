// Model A: the vector is a seq, and the range-for is a `for` over a copy of it.
// A seq is a value, so appending to v cannot change the loop, and the model says the sum of the old elements.
// The bounds keep every partial sum in int32.
newtype int32 = x: int | -0x8000_0000 <= x < 0x8000_0000

function Sum(s: seq<int32>): int
  decreases |s|
{
  if |s| == 0 then 0 else Sum(s[..|s| - 1]) + (s[|s| - 1] as int)
}

method sum_and_double(v0: seq<int32>) returns (result: int32, v: seq<int32>)
  requires 0 < |v0| <= 1000
  requires forall i :: 0 <= i < |v0| ==> 0 <= v0[i] <= 1000
  ensures result as int == Sum(v0)
{
  v := v0;
  var s: int32 := 0;
  for i := 0 to |v0|
    invariant 0 <= s as int <= i * 1000
    invariant s as int == Sum(v0[..i])
  {
    assert v0[..i + 1] == v0[..i] + [v0[i]];
    s := s + v0[i];
    v := v + [v0[i]];
  }
  assert v0[..|v0|] == v0;
  result := s;
}
