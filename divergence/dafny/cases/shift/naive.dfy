// Model A: bit-vectors, because Dafny has no shift on int. Dafny asks for n <= 32, and the model gets it.
// Dafny allows a shift by the full width, and the result is 0. C++ does not allow it.
method shl(x: bv32, n: bv32) returns (result: bv32)
  requires n <= 32
  ensures result == x << n
{
  result := x << n;
}

method Demo() {
  var r := shl(1, 32);
  assert r == 0;
}
