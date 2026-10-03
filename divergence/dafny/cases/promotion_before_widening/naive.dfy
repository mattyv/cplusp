// Model A: the product is taken in unbounded integers, because the result is an int64. It fits, so Dafny proves it.
// C++ multiplies two int32_t first. The wide result type does not change the type of the product.
newtype int32 = x: int | -0x8000_0000 <= x < 0x8000_0000
newtype int64 = x: int | -0x8000_0000_0000_0000 <= x < 0x8000_0000_0000_0000

method product(a: int32, b: int32) returns (result: int64)
  ensures result as int == (a as int) * (b as int)
{
  result := ((a as int) * (b as int)) as int64;
}

// The model proves 10000000000. C++ has undefined behaviour.
method Demo() {
  var r := product(100000, 100000);
  assert r == 10000000000;
}
