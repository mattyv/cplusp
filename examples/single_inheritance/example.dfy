// The base is a trait, and the derived class extends it. The trait function promises corners() >= 3, and the override
// promises 4, which implies it. A caller through the base knows 3 or more, and a caller of the Square knows 4.
newtype int32 = x: int | -0x8000_0000 <= x < 0x8000_0000

trait Shape {
  function corners(): int32
    ensures corners() >= 3
}

class Square extends Shape {
  constructor () {}

  function corners(): int32
    ensures corners() == 4
  {
    4
  }
}

method count_corners(s: Shape) returns (result: int32)
  ensures result >= 3
{
  result := s.corners();
}

method square_corners(q: Square) returns (result: int32)
  ensures result == 4
{
  result := q.corners();
}
