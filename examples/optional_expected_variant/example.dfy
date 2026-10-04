// An optional is a datatype with None and Some. `*h` is `h.value`, and Dafny asks for a proof that h is Some, which the
// has_value test gives. x / 2 and x % 2 are used on an even number only, where Dafny and C++ agree.
newtype int32 = x: int | -0x8000_0000 <= x < 0x8000_0000

datatype Option<T> = None | Some(value: T)

method half_of_even(x: int32) returns (result: Option<int32>)
  ensures result.Some? == (x % 2 == 0)
  ensures result.Some? ==> result.value == x / 2
{
  if x % 2 != 0 {
    result := None;
  } else {
    result := Some(x / 2);
  }
}

method half_or(x: int32, fallback: int32) returns (result: int32)
  ensures result == (if x % 2 == 0 then x / 2 else fallback)
{
  var h := half_of_even(x);
  if !h.Some? {
    return fallback;
  }
  return h.value;
}
