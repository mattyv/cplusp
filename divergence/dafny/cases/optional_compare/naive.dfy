// Model A: std::optional as a datatype, and `o == 5` and `o < 5` as the comparison of the field.
// Dafny asks for a proof that o holds a value. There is none, so the model is stricter than C++.
// The C++ compares an empty optional with a value, and the result is defined.
newtype int32 = x: int | -0x8000_0000 <= x < 0x8000_0000

datatype Option<T> = None | Some(value: T)

method is_five(o: Option<int32>) returns (result: bool)
  ensures result == (o.Some? && o.value == 5)
{
  result := o.value == 5;
}

method below_five(o: Option<int32>) returns (result: bool)
  ensures result == (o.None? || o.value < 5)
{
  result := o.value < 5;
}
