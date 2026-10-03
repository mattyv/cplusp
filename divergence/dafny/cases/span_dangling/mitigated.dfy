// Model B: the C++ copies the element out, so first is a value in the C++ too, and this model is exact.
// The model has no span, because the gate allows a span as a parameter only.
newtype int32 = x: int | -0x8000_0000 <= x < 0x8000_0000

method first_after_grow(v0: seq<int32>) returns (result: int32, v: seq<int32>)
  requires |v0| > 0
  ensures result == v0[0]
{
  v := v0;
  var first: int32 := v[0];
  v := v + [1];
  result := first;
}
