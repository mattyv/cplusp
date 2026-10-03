// Model B: C++ computes `a + 100` in int, then converts back to uint8_t, which is modular.
newtype int32 = x: int | -0x8000_0000 <= x < 0x8000_0000
newtype uint8 = x: int | 0 <= x < 0x100

function wrap8(x: int): uint8 {
  (x % 0x100) as uint8
}

method bump(a: uint8) returns (result: uint8)
  ensures result as int == ((a as int) + 100) % 0x100
{
  var b: uint8 := a;
  var sum: int32 := (b as int32) + 100;
  b := wrap8(sum as int);
  result := b;
}
