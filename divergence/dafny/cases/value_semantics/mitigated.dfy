// Model B: the struct is a datatype, a value. A copy is the same value, and a field update is a new value.
newtype int32 = x: int | -0x8000_0000 <= x < 0x8000_0000

datatype Point = Point(x: int32, y: int32)

method keep(p: Point) returns (result: int32)
  requires p.x <= 0x7FFF_FFFA
  ensures result as int == p.x as int + 5
{
  var q := p;
  q := q.(x := 5);
  result := p.x + q.x;
}

// The model proves 6 for p.x == 1, and so does C++.
method Demo() {
  var r := keep(Point(1, 2));
  assert r == 6;
}
