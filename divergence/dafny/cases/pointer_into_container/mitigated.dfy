// Model B: the C++ copies the element out, so `&first` points at a local that no push_back moves, and this model is exact.
// A pointer is an Option value and the vector is a seq, decision 0029. They cannot alias, and the gate keeps a pointer
// into a container out of the C++ for that reason. The same text is right for `&first` and wrong for `&v[0]`.
newtype int32 = x: int | -0x8000_0000 <= x < 0x8000_0000

datatype Option<T> = None | Some(value: T)

method read_after_grow(v0: seq<int32>, p: Option<int32>) returns (result: int32, v: seq<int32>)
  requires p.Some?
  ensures result == p.value
{
  v := v0 + [1];
  result := p.value;
}

method first_then_grow(v0: seq<int32>) returns (result: int32, v: seq<int32>)
  requires |v0| > 0
  ensures result == v0[0]
{
  var first := v0[0];
  result, v := read_after_grow(v0, Some(first));
}
