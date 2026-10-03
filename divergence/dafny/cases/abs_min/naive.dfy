// Model A: `std::abs` as `if x < 0 then -x else x`. Dafny asks for a proof that `-x` fits.
// For -0x8000_0000 there is none.
newtype int32 = x: int | -0x8000_0000 <= x < 0x8000_0000

method magnitude(x: int32) returns (result: int32)
  ensures result as int == (if x < 0 then -(x as int) else x as int)
{
  result := if x < 0 then -x else x;
}
