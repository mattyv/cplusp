// The interface is an opaque type, decision 0029, and its contract is the promise of every implementation. The invariant of the C++
// classes is the predicate Valid, which the constructors establish. The interface cannot know the fields, so its Valid is a predicate
// with no body, and each class proves its own contract on its own datatype. A vector of unique_ptr is a seq of Option values, and a
// null test is `Some?`. The sum proves from the interface contract alone, for a seq of the opaque type. The conversion from a class to
// the interface is trusted, as the vtable is. A product of two bounded numbers is a nonlinear fact, so a lemma proves it.
newtype int32 = x: int | -0x8000_0000 <= x < 0x8000_0000
newtype int64 = x: int | -0x8000_0000_0000_0000 <= x < 0x8000_0000_0000_0000

datatype Option<T> = None | Some(value: T)

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
  ensures (ProductAtMost(q.side as int, q.side as int); square_area(q) == q.side * q.side)
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
  ensures (ProductAtMost(r.w as int, r.h as int); rect_area(r) == r.w * r.h)
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

method total_area(shapes: seq<Option<Shape>>) returns (result: int64)
  requires |shapes| <= 1000
  requires forall i :: 0 <= i < |shapes| ==> shapes[i].Some?
  requires forall i :: 0 <= i < |shapes| ==> Valid(shapes[i].value)
  ensures 0 <= result <= 1_000_000_000
{
  var total: int64 := 0;
  var i := 0;
  while i < |shapes|
    invariant 0 <= i <= |shapes|
    invariant 0 <= total as int <= 1_000_000 * i
    decreases |shapes| - i
  {
    var a := area(shapes[i].value);
    total := total + (a as int64);
    i := i + 1;
  }
  result := total;
}

method sample_total() returns (result: int64)
  ensures 0 <= result <= 1_000_000_000
{
  var sq := MakeSquare(5);
  var r := MakeRect(2, 3);
  var shapes: seq<Option<Shape>> := [Some(SquareAsShape(sq)), Some(RectAsShape(r))];
  result := total_area(shapes);
}
