// Model B: the contract says the value is an enumerator. The caller carries the obligation.
newtype uint8 = x: int | 0 <= x < 0x100

datatype Mode = Fast | Slow

method to_mode(v: uint8) returns (result: Mode)
  requires v < 2
  ensures result == (if v == 0 then Fast else Slow)
{
  match v {
    case 0 => result := Fast;
    case 1 => result := Slow;
  }
}
