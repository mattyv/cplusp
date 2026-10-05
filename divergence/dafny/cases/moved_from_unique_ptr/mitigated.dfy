// Model B: a unique_ptr is an Option value, decision 0029. A move copies the value and sets the source to None. A read of the
// source is then a read of a value that is not Some, and Dafny refuses it. Put `p.value` in place of `q.value` below and the
// proof fails. The C++ contract names the value on the way in, `old(*p)`, and the model names the input `p0`.
newtype int32 = x: int | -0x8000_0000 <= x < 0x8000_0000

datatype Option<T> = None | Some(value: T)

method take(p0: Option<int32>) returns (result: int32)
  requires p0.Some?
  requires -0x4000_0000 <= p0.value < 0x4000_0000
  ensures result as int == 2 * (p0.value as int)
{
  var p := p0;
  var q := p;
  p := None;
  result := q.value + q.value;
}

// The model proves 14, and so does the fixed C++.
method Demo() {
  var r := take(Some(7));
  assert r == 14;
}
