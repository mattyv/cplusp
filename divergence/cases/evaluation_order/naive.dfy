// Model A: Dafny has no method call inside an expression, so the arguments are hoisted left to right.
// C++ does not promise that order. clang takes it. g++ evaluates the arguments right to left and returns false.
newtype int32 = x: int | -0x8000_0000 <= x < 0x8000_0000

class Ref {
  var v: int32
}

method next(x: Ref) returns (result: int32)
  requires x.v < 0x7FFF_FFFF
  modifies x
  ensures x.v as int == old(x.v) as int + 1
  ensures result == old(x.v)
{
  result := x.v;
  x.v := x.v + 1;
}

function before(a: int32, b: int32): bool {
  a < b
}

method rises(x: Ref) returns (result: bool)
  requires x.v < 0x7FFF_FFFE
  modifies x
  ensures x.v as int == old(x.v) as int + 2
  ensures result == true
{
  var first := next(x);
  var second := next(x);
  result := before(first, second);
}
