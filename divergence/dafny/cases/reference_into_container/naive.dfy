// Model A: the vector is a seq, a value, and the reference r is the element read out of it.
// A seq element is a value, so `v := v + [1]` cannot change r, and the proof holds.
newtype int32 = x: int | -0x8000_0000 <= x < 0x8000_0000

method first_then_grow(v0: seq<int32>) returns (result: int32, v: seq<int32>)
  requires |v0| > 0
  ensures result == v0[0]
{
  v := v0;
  var r := v[0];
  v := v + [1];
  result := r;
}
