// The base is an opaque type, decision 0029, and its contract is the only thing known about it: corners(s) >= 3. The derived class
// is a datatype with its own function. The lemma is the override check. The promise of Square, 4, implies the promise of the base,
// 3 or more. A caller through the base knows 3 or more, and a caller of the Square knows 4.
newtype int32 = x: int | -0x8000_0000 <= x < 0x8000_0000

type Shape

function {:axiom} corners(s: Shape): int32
  ensures corners(s) >= 3

datatype Square = Square

function square_corners_of(q: Square): int32
  ensures square_corners_of(q) == 4
{
  4
}

lemma SquareKeepsThePromiseOfShape(q: Square)
  ensures square_corners_of(q) >= 3
{
}

method count_corners(s: Shape) returns (result: int32)
  ensures result >= 3
{
  result := corners(s);
}

method square_corners(q: Square) returns (result: int32)
  ensures result == 4
{
  result := square_corners_of(q);
}
