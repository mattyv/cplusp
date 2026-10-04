// A template has no model. Each instantiation is a method with its own types, larger_int32 and larger_uint8, and the callers
// call the model of the instantiation they use.
newtype int32 = x: int | -0x8000_0000 <= x < 0x8000_0000
newtype uint8 = x: int | 0 <= x < 0x100

method larger_int32(a: int32, b: int32) returns (result: int32)
  ensures result >= a && result >= b && (result == a || result == b)
{
  if a < b {
    result := b;
  } else {
    result := a;
  }
}

method larger_uint8(a: uint8, b: uint8) returns (result: uint8)
  ensures result >= a && result >= b && (result == a || result == b)
{
  if a < b {
    result := b;
  } else {
    result := a;
  }
}

method larger32(a: int32, b: int32) returns (result: int32)
  ensures result >= a && result >= b && (result == a || result == b)
{
  result := larger_int32(a, b);
}

method larger8(a: uint8, b: uint8) returns (result: uint8)
  ensures result >= a && result >= b && (result == a || result == b)
{
  result := larger_uint8(a, b);
}
