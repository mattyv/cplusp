// Model A: `enum class Mode` as a datatype of its enumerators, and the cast as a match on the integer.
// The cast has a case for each enumerator. It has none for 7, so Dafny does not accept it.
newtype uint8 = x: int | 0 <= x < 0x100

datatype Mode = Fast | Slow

method to_mode(v: uint8) returns (result: Mode)
  ensures result == (if v == 0 then Fast else Slow)
{
  match v {
    case 0 => result := Fast;
    case 1 => result := Slow;
  }
}
