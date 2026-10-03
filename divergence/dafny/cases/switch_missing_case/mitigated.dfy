// Model B: the C++ has a case for every enumerator, so the match covers every value and is exact.
newtype int32 = x: int | -0x8000_0000 <= x < 0x8000_0000

datatype Mode = Fast | Slow

method pick(m: Mode) returns (result: int32)
  ensures result == (if m == Fast then 1 else 2)
{
  match m {
    case Fast => result := 1;
    case Slow => result := 2;
  }
}
