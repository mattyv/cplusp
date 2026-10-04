// The method carries `decreases |v| - i`, and Dafny proves the recursion ends. Dafny does not prove that the stack holds the depth,
// so the contract bounds it, `requires |v| <= 10000`. Count is the specification, over the rest of the sequence.
newtype int32 = x: int | -0x8000_0000 <= x < 0x8000_0000
newtype uint64 = x: int | 0 <= x < 0x1_0000_0000_0000_0000

function Count(s: seq<int32>, x: int32): int
  decreases |s|
{
  if |s| == 0 then 0 else (if s[0] == x then 1 else 0) + Count(s[1..], x)
}

method count_equal(v: seq<int32>, i: uint64, x: int32) returns (result: uint64)
  requires |v| <= 10000
  requires i as int <= |v|
  decreases |v| - i as int
  ensures result as int <= |v| - i as int
  ensures result as int == Count(v[i..], x)
{
  if i as int == |v| {
    return 0;
  }
  var rest := count_equal(v, i + 1, x);
  assert v[i..][1..] == v[i + 1..];
  if v[i] == x {
    return rest + 1;
  }
  return rest;
}
