// Model A: `constexpr` is dropped, and the function is a method with the contract written in the C++.
// Dafny refuses the product, because it may overflow int32. The model is stricter than the C++.
newtype int32 = x: int | -0x8000_0000 <= x < 0x8000_0000

method square(x: int32) returns (result: int32)
  ensures result as int == (x as int) * (x as int)
{
  result := x * x;
}
