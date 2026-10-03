// Model A: `/` and `%` carried over as they are. Dafny rounds toward negative infinity, C++ toward zero.
newtype int32 = x: int | -0x8000_0000 <= x < 0x8000_0000

method quot(a: int32, b: int32) returns (result: int32)
  requires b != 0
  requires !(a == -0x8000_0000 && b == -1)
  ensures result == a / b
{
  result := a / b;
}

method rem(a: int32, b: int32) returns (result: int32)
  requires b != 0
  requires !(a == -0x8000_0000 && b == -1)
  ensures result == a % b
{
  result := a % b;
}

// The model proves -4 and 1. C++ gives -3 and -1.
method Demo() {
  var q := quot(-7, 2);
  var r := rem(-7, 2);
  assert q == -4 && r == 1;
}
