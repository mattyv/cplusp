// Model B: the contract says the optional holds a value. The caller carries the obligation.
newtype int32 = x: int | -0x8000_0000 <= x < 0x8000_0000

datatype Option<T> = None | Some(value: T)

method value(opt: Option<int32>) returns (result: int32)
  requires opt.Some?
  ensures result == opt.value
{
  result := opt.value;
}
