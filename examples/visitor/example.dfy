// Two interfaces, Shape and Visitor, and no trait, decision 0029. Each is an opaque type with its contract as the only functions
// known about it. The calls that change the visitor are methods without a body, since they take the visitor in and give it back.
// Each class proves its own contract on its own datatype. Square.accept is the double dispatch: it calls the visit for Square on the
// visitor it is given. AreaSum meets the contract of Visitor on its own value. The conversions from a class to an interface are
// trusted, as the vtables are, and say only what a const function reads. After the driver changes the visitor through the
// interface, the model reads it through the interface again: the dispatch is a call on the same value. The driver proves its bound
// from the two contracts alone.
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
type Visitor

predicate {:axiom} ValidShape(s: Shape)

function {:axiom} area(s: Shape): int32
  requires ValidShape(s)
  ensures 0 <= area(s) <= 1_000_000

predicate {:axiom} ValidVisitor(v: Visitor)

function {:axiom} seen(v: Visitor): int64
  requires ValidVisitor(v)
  ensures seen(v) >= 0

method {:axiom} accept(s: Shape, v: Visitor) returns (v': Visitor)
  requires ValidShape(s) && ValidVisitor(v) && seen(v) <= 1_000_000_000
  ensures ValidVisitor(v') && seen(v') as int == seen(v) as int + area(s) as int

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

method {:axiom} visit_square(v: Visitor, s: Square) returns (v': Visitor)
  requires ValidVisitor(v) && ValidSquare(s) && seen(v) <= 1_000_000_000
  ensures ValidVisitor(v') && seen(v') as int == seen(v) as int + square_area(s) as int

method {:axiom} visit_rect(v: Visitor, r: Rect) returns (v': Visitor)
  requires ValidVisitor(v) && ValidRect(r) && seen(v) <= 1_000_000_000
  ensures ValidVisitor(v') && seen(v') as int == seen(v) as int + rect_area(r) as int

// The override check for accept. Each class meets the contract of Shape.accept, and the body is the callback.
method square_accept(q: Square, v: Visitor) returns (v': Visitor)
  requires ValidSquare(q) && ValidVisitor(v) && seen(v) <= 1_000_000_000
  ensures ValidVisitor(v') && seen(v') as int == seen(v) as int + square_area(q) as int
{
  v' := visit_square(v, q);
}

method rect_accept(r: Rect, v: Visitor) returns (v': Visitor)
  requires ValidRect(r) && ValidVisitor(v) && seen(v) <= 1_000_000_000
  ensures ValidVisitor(v') && seen(v') as int == seen(v) as int + rect_area(r) as int
{
  v' := visit_rect(v, r);
}

function {:axiom} SquareAsShape(q: Square): Shape
  ensures ValidShape(SquareAsShape(q)) == ValidSquare(q)
  ensures ValidSquare(q) ==> area(SquareAsShape(q)) == square_area(q)

function {:axiom} RectAsShape(r: Rect): Shape
  ensures ValidShape(RectAsShape(r)) == ValidRect(r)
  ensures ValidRect(r) ==> area(RectAsShape(r)) == rect_area(r)

// The concrete visitor. Its methods meet the contract of Visitor on its own type.
datatype AreaSum = AreaSum(total: int64)

predicate ValidAreaSum(a: AreaSum) { 0 <= a.total <= 2_000_000_000 }

method MakeAreaSum() returns (a: AreaSum)
  ensures ValidAreaSum(a) && a.total == 0
{
  a := AreaSum(0);
}

function area_sum_seen(a: AreaSum): int64
  requires ValidAreaSum(a)
  ensures area_sum_seen(a) >= 0
{
  a.total
}

method area_sum_visit_square(a: AreaSum, s: Square) returns (a': AreaSum)
  requires ValidAreaSum(a) && ValidSquare(s) && a.total <= 1_000_000_000
  ensures ValidAreaSum(a') && a'.total as int == a.total as int + square_area(s) as int
{
  a' := AreaSum(a.total + (square_area(s) as int64));
}

method area_sum_visit_rect(a: AreaSum, r: Rect) returns (a': AreaSum)
  requires ValidAreaSum(a) && ValidRect(r) && a.total <= 1_000_000_000
  ensures ValidAreaSum(a') && a'.total as int == a.total as int + rect_area(r) as int
{
  a' := AreaSum(a.total + (rect_area(r) as int64));
}

function {:axiom} AreaSumAsVisitor(a: AreaSum): Visitor
  ensures ValidVisitor(AreaSumAsVisitor(a)) == ValidAreaSum(a)
  ensures ValidAreaSum(a) ==> seen(AreaSumAsVisitor(a)) == area_sum_seen(a)

method visit_all(shapes: seq<Option<Shape>>, v0: Visitor) returns (v: Visitor)
  requires |shapes| <= 1000
  requires forall i :: 0 <= i < |shapes| ==> shapes[i].Some?
  requires forall i :: 0 <= i < |shapes| ==> ValidShape(shapes[i].value)
  requires ValidVisitor(v0) && seen(v0) == 0
  ensures ValidVisitor(v) && 0 <= seen(v) as int <= 1_000_000 * |shapes|
{
  v := v0;
  var i := 0;
  while i < |shapes|
    invariant 0 <= i <= |shapes|
    invariant ValidVisitor(v) && 0 <= seen(v) as int <= 1_000_000 * i
    decreases |shapes| - i
  {
    v := accept(shapes[i].value, v);
    i := i + 1;
  }
}

method total_area(shapes: seq<Option<Shape>>) returns (result: int64)
  requires |shapes| <= 1000
  requires forall i :: 0 <= i < |shapes| ==> shapes[i].Some?
  requires forall i :: 0 <= i < |shapes| ==> ValidShape(shapes[i].value)
  ensures 0 <= result <= 1_000_000_000
{
  var sum := MakeAreaSum();
  var v := AreaSumAsVisitor(sum);
  v := visit_all(shapes, v);
  result := seen(v);
}

method sample_total() returns (result: int64)
  ensures 0 <= result <= 1_000_000_000
{
  var sq := MakeSquare(5);
  var r := MakeRect(2, 3);
  var shapes: seq<Option<Shape>> := [Some(SquareAsShape(sq)), Some(RectAsShape(r))];
  result := total_area(shapes);
}
