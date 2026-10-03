// Model B: the C++ copies the element out, so r is a value in the C++ too, and this model is exact.
// The same text as model A is right for `int32_t r = v[0];` and wrong for `const int32_t& r = v[0];`.
newtype int32 = x: int | -0x8000_0000 <= x < 0x8000_0000

method first_then_grow(v0: seq<int32>) returns (result: int32, v: seq<int32>)
  requires |v0| > 0
  ensures result == v0[0]
{
  v := v0;
  var r: int32 := v[0];
  v := v + [1];
  result := r;
}
