// Model A: Mode is a datatype of its enumerators, and the switch is a match with one arm.
// Dafny reports the missing case for Slow. The model is stricter than C++.
// The C++ runs past the switch for Slow, and returns 0 in silence.
newtype int32 = x: int | -0x8000_0000 <= x < 0x8000_0000

datatype Mode = Fast | Slow

method pick(m: Mode) returns (result: int32)
  ensures result == (if m == Fast then 1 else 2)
{
  match m {
    case Fast => result := 1;
  }
}
