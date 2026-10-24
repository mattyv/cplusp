// Each instance of the template is a method with its own types, c_larger'of'int32 and c_larger'of'uint8, decision 0180. The
// callers call the method of the instance that they use.
newtype int32 = x: int | -0x8000_0000 <= x < 0x8000_0000
newtype uint8 = x: int | 0 <= x < 0x100

method c_larger'of'int32(a: int32, b: int32) returns (result: int32)
  ensures result >= a && result >= b && (result == a || result == b)
{
  if a < b {
    result := b;
  } else {
    result := a;
  }
}

method c_larger'of'uint8(a: uint8, b: uint8) returns (result: uint8)
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
  result := c_larger'of'int32(a, b);
}

method larger8(a: uint8, b: uint8) returns (result: uint8)
  ensures result >= a && result >= b && (result == a || result == b)
{
  result := c_larger'of'uint8(a, b);
}
