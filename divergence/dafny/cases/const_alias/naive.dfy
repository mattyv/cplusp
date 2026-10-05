// Model A: a const reference is a value in, and a non-const reference is a value in and a value out. The two are separate.
// The model proves that the result is the value `b` held at the call, and says 0 for set_and_read(x, x). The C++ returns 1.
newtype int32 = x: int | -0x8000_0000 <= x < 0x8000_0000

method set_and_read(a: int32, b: int32) returns (a': int32, result: int32)
  ensures a' == 1 && result == b
{
  a' := 1;
  result := b;
}

method Demo() {
  var x: int32 := 0;
  var x', r := set_and_read(x, x);
  assert r == 0;
}
