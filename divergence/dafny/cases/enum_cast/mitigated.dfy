// Model B: the C++ maps the number to an enumerator, because the gate bans the cast, row enum_cast. The model is the same map.
newtype uint8 = x: int | 0 <= x < 0x100

datatype Mode = Fast | Slow

method to_mode(v: uint8) returns (result: Mode)
  ensures result == (if v == 0 then Fast else Slow)
{
  if v == 0 {
    result := Fast;
  } else {
    result := Slow;
  }
}
