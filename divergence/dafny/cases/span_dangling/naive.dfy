// Model A: the vector is a seq, a value, and the span s is a copy of it.
// A seq is a value, so `v := v + [1]` cannot change s, and the proof holds.
newtype int32 = x: int | -0x8000_0000 <= x < 0x8000_0000

method first_after_grow(v0: seq<int32>) returns (result: int32, v: seq<int32>)
  requires |v0| > 0
  ensures result == v0[0]
{
  v := v0;
  var s: seq<int32> := v;
  v := v + [1];
  result := s[0];
}
