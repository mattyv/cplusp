// An overloaded operator is a function. So `a + b` on a class type is a call to it with its own contract, never the built-in
// plus. The struct is a datatype. The contract of the operator is the one the caller proves from.
newtype int32 = x: int | -0x8000_0000 <= x < 0x8000_0000

datatype Point = Point(x: int32, y: int32)

function Plus(a: Point, b: Point): Point
  requires -0x4000_0000 <= a.x < 0x4000_0000 && -0x4000_0000 <= b.x < 0x4000_0000
  requires -0x4000_0000 <= a.y < 0x4000_0000 && -0x4000_0000 <= b.y < 0x4000_0000
  ensures Plus(a, b).x == a.x + b.x && Plus(a, b).y == a.y + b.y
{
  Point(a.x + b.x, a.y + b.y)
}

method shifted(p: Point) returns (result: Point)
  requires -0x4000_0000 <= p.x < 0x4000_0000 && -0x4000_0000 <= p.y < 0x4000_0000
  ensures result.x == p.x + 1 && result.y == p.y + 1
{
  result := Plus(p, Point(1, 1));
}
