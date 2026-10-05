// The interface is an opaque type, decision 0029, and its contract is the only thing a caller of the factory knows. The factory
// returns an Option of it, as a unique_ptr does, and a null test is `Some?`. Each class proves its own contract on its own datatype.
// The conversion from a class to the interface is trusted, as the vtable is. The caller proves its bound from the interface
// contract alone, so it never names Square or Rect. A product of two bounded numbers is a nonlinear fact, so a lemma proves it.
newtype int32 = x: int | -0x8000_0000 <= x < 0x8000_0000

datatype Option<T> = None | Some(value: T)

datatype Kind = SquareKind | RectKind

lemma NonnegProduct(a: int, b: int)
  requires a >= 0 && b >= 0
  ensures a * b >= 0
  decreases a
{
  if a > 0 {
    NonnegProduct(a - 1, b);
  }
}

lemma ProductAtMost(a: int, b: int)
  requires 0 <= a <= 1000 && 0 <= b <= 1000
  ensures 0 <= a * b <= 1_000_000
{
  NonnegProduct(a, b);
  NonnegProduct(1000 - a, 1000);
  NonnegProduct(a, 1000 - b);
}

type Shape

predicate {:axiom} Valid(s: Shape)

function {:axiom} area(s: Shape): int32
  requires Valid(s)
  ensures 0 <= area(s) <= 1_000_000

datatype Square = Square(side: int32)

predicate ValidSquare(q: Square) { 0 <= q.side <= 1000 }

method MakeSquare(side: int32) returns (q: Square)
  requires 0 <= side <= 1000
  ensures ValidSquare(q) && q.side == side
{
  q := Square(side);
}

function square_area(q: Square): int32
  requires ValidSquare(q)
  ensures 0 <= square_area(q) <= 1_000_000
  ensures square_area(q) == q.side * q.side
{
  ProductAtMost(q.side as int, q.side as int);
  q.side * q.side
}

datatype Rect = Rect(w: int32, h: int32)

predicate ValidRect(r: Rect) { 0 <= r.w <= 1000 && 0 <= r.h <= 1000 }

method MakeRect(w: int32, h: int32) returns (r: Rect)
  requires 0 <= w <= 1000 && 0 <= h <= 1000
  ensures ValidRect(r) && r.w == w && r.h == h
{
  r := Rect(w, h);
}

function rect_area(r: Rect): int32
  requires ValidRect(r)
  ensures 0 <= rect_area(r) <= 1_000_000
  ensures rect_area(r) == r.w * r.h
{
  ProductAtMost(r.w as int, r.h as int);
  r.w * r.h
}

function {:axiom} SquareAsShape(q: Square): Shape
  ensures Valid(SquareAsShape(q)) == ValidSquare(q)
  ensures ValidSquare(q) ==> area(SquareAsShape(q)) == square_area(q)

function {:axiom} RectAsShape(r: Rect): Shape
  ensures Valid(RectAsShape(r)) == ValidRect(r)
  ensures ValidRect(r) ==> area(RectAsShape(r)) == rect_area(r)

method make_shape(k: Kind, size: int32) returns (result: Option<Shape>)
  requires 0 <= size <= 1000
  ensures result.Some? && Valid(result.value)
{
  if k == SquareKind {
    var q := MakeSquare(size);
    result := Some(SquareAsShape(q));
  } else {
    var r := MakeRect(size, 2);
    result := Some(RectAsShape(r));
  }
}

method area_of(k: Kind, size: int32) returns (result: int32)
  requires 0 <= size <= 1000
  ensures 0 <= result <= 1_000_000
{
  var s := make_shape(k, size);
  result := area(s.value);
}
