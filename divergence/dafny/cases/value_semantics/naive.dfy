// Model A: the struct is a Dafny class, as every object in Dafny is.
// `var q := p` then makes a second name for one object, and the update of q.x changes p.x.
// Dafny asks for `modifies p`, and with it the contract holds, with p.x read after the call.
newtype int32 = x: int | -0x8000_0000 <= x < 0x8000_0000

class Point {
  var x: int32
  var y: int32
}

method keep(p: Point) returns (result: int32)
  requires p.x <= 0x7FFF_FFFA
  modifies p
  ensures result as int == p.x as int + 5
{
  var q := p;
  q.x := 5;
  result := p.x + q.x;
}

// The model proves 10 for p.x == 1. In C++ q is a copy, and the result is 6.
method Demo() {
  var p := new Point;
  p.x := 1;
  var q := p;
  q.x := 5;
  assert p.x + q.x == 10;
}
