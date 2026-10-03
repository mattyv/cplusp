// Model B: the empty case is written out. An empty optional is not equal to a value, and it is less than every value.
newtype int32 = x: int | -0x8000_0000 <= x < 0x8000_0000

datatype Option<T> = None | Some(value: T)

method is_five(o: Option<int32>) returns (result: bool)
  ensures result == (o.Some? && o.value == 5)
{
  result := o.Some? && o.value == 5;
}

method below_five(o: Option<int32>) returns (result: bool)
  ensures result == (o.None? || o.value < 5)
{
  result := o.None? || o.value < 5;
}
