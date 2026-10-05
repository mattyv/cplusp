// A range-for is a loop over a seq, and the body reads each element. The model loops by index. The invariant says what the total is
// after the first i elements. A bound on it keeps the sum inside int32, and `decreases` shows that the loop ends. Sum is the
// specification, and `Sum(v)` in the C++ contract is this function.
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
    decreases |v| - i
  {
    assert v[..i + 1][..i] == v[..i];
    t := t + v[i];
    i := i + 1;
  }
  assert v[..i] == v;
  result := t;
}
