// A unique_ptr<int32_t> is an Option value, decision 0029. make_unique gives Some, and the box is the only owner.
// A read needs `p.Some?`, in the C++ as `requires p != nullptr`, and the caller carries it.
newtype int32 = x: int | -0x8000_0000 <= x < 0x8000_0000

datatype Option<T> = None | Some(value: T)

method boxed(x: int32) returns (result: Option<int32>)
  ensures result.Some? && result.value == x
{
  result := Some(x);
}

method unboxed(p: Option<int32>) returns (result: int32)
  requires p.Some?
  ensures result == p.value
{
  result := p.value;
}

method round_trip(x: int32) returns (result: int32)
  ensures result == x
{
  var p := boxed(x);
  result := unboxed(p);
}
