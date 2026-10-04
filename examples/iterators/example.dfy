// A range-for is a loop over a seq, and the body reads each element. The invariant says what the total is after the first i
// elements, and a bound on it keeps the sum inside int32. Sum is the specification, and `sum(v)` in the C++ is the same function.
newtype int32 = x: int | -0x8000_0000 <= x < 0x8000_0000

function Sum(s: seq<int32>): int
  decreases |s|
{
  if |s| == 0 then 0 else Sum(s[..|s| - 1]) + s[|s| - 1] as int
}

method total(v: seq<int32>) returns (result: int32)
  requires |v| <= 1000
  requires forall j :: 0 <= j < |v| ==> -1000 <= v[j] <= 1000
  ensures result as int == Sum(v)
{
  var t: int32 := 0;
  var i := 0;
  while i < |v|
    invariant 0 <= i <= |v|
    invariant t as int == Sum(v[..i])
    invariant -1000 * i <= t as int <= 1000 * i
  {
    assert v[..i + 1][..i] == v[..i];
    t := t + v[i];
    i := i + 1;
  }
  assert v[..i] == v;
  result := t;
}
