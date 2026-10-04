// Model A: the conversion is `Floor`, and `trunc` is `Floor`. Dafny fails the range check, because x may be outside int32.
// The model is stricter than the C++, which does not check. Also Floor(-3.7) is -4, and the C++ gives -3.
newtype int32 = x: int | -0x8000_0000 <= x < 0x8000_0000

function trunc(x: real): int { x.Floor }

method whole(x: real) returns (result: int32)
  ensures result as int == trunc(x)
{
  result := x.Floor as int32;
}
