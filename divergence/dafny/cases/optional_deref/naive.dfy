// Model A: std::optional as a datatype, and `*opt` as the field. Dafny asks for a proof that opt holds a value.
newtype int32 = x: int | -0x8000_0000 <= x < 0x8000_0000

datatype Option<T> = None | Some(value: T)

method value(opt: Option<int32>) returns (result: int32)
  ensures result == opt.value
{
  result := opt.value;
}
