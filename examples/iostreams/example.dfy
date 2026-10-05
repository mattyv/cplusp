// The model has no I/O. The verified function is a method with a proof, and the trusted print is an axiom method with a
// precondition and no effect on anything the model sees. The caller proves the precondition from the first method's contract.
newtype int32 = x: int | -0x8000_0000 <= x < 0x8000_0000
newtype int64 = x: int | -0x8000_0000_0000_0000 <= x < 0x8000_0000_0000_0000

method percent(part: int32, whole: int32) returns (result: int32)
  requires 0 < whole && 0 <= part <= whole
  ensures 0 <= result <= 100
{
  var p: int := part as int;
  var w: int := whole as int;
  var q: int := (p * 100) / w;
  // The quotient is at most 100: the numerator is at most 100 * w, and division by a positive w keeps the order.
  assert p * 100 <= w * 100;
  assert (w * 100) / w == 100;
  assert (p * 100) / w <= (w * 100) / w;
  result := q as int32;
}

method {:axiom} print_percent(p: int32)
  requires 0 <= p <= 100

method report(part: int32, whole: int32)
  requires 0 < whole && 0 <= part <= whole
{
  var p := percent(part, whole);
  print_percent(p);
}
