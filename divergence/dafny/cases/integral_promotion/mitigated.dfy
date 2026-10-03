// Model B: C++ adds uint8_t in int, then converts back to uint8_t, which is modular.
newtype int32 = x: int | -0x8000_0000 <= x < 0x8000_0000
newtype uint8 = x: int | 0 <= x < 0x100

function wrap8(x: int): uint8 {
  (x % 0x100) as uint8
}

method add8(a: uint8, b: uint8) returns (result: uint8)
  ensures result as int == ((a as int) + (b as int)) % 0x100
{
  var sum: int32 := (a as int32) + (b as int32);
  result := wrap8(sum as int);
}
