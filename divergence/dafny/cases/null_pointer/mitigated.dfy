// Model B: a pointer is an Option value, decision 0029. The contract says the pointer is not null, in the C++ as
// `requires p != nullptr` and here as `requires p.Some?`. The caller carries the obligation.
newtype int32 = x: int | -0x8000_0000 <= x < 0x8000_0000

datatype Option<T> = None | Some(value: T)

method read(p: Option<int32>) returns (result: int32)
  requires p.Some?
  ensures result == p.value
{
  result := p.value;
}
