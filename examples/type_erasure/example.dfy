// A class template has no model, and neither has a constructor template. Each type they are used at gets its own datatype and its own
// method: ModelSquare and ModelRect for Model<T>, MakeShapeSquare and MakeShapeRect for the constructor of Shape. The interface is an
// opaque type, decision 0029, and the wrapper holds it as an Option, as a unique_ptr member is. The conversions to the interface say
// only what a const function reads, and are trusted, as the vtables are. A product of two bounded numbers is a nonlinear fact, so a
// lemma proves it.
newtype int32 = x: int | -0x8000_0000 <= x < 0x8000_0000

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

datatype Square = Square(side: int32)

predicate ValidSquare(q: Square) { 0 <= q.side <= 1000 }

function square_area(q: Square): int32
  requires ValidSquare(q)
  ensures 0 <= square_area(q) <= 1_000_000 && square_area(q) == q.side * q.side
{
  ProductAtMost(q.side as int, q.side as int);
  q.side * q.side
}

datatype Rect = Rect(w: int32, h: int32)

predicate ValidRect(r: Rect) { 0 <= r.w <= 1000 && 0 <= r.h <= 1000 }

function rect_area(r: Rect): int32
  requires ValidRect(r)
  ensures 0 <= rect_area(r) <= 1_000_000 && rect_area(r) == r.w * r.h
{
  ProductAtMost(r.w as int, r.h as int);
  r.w * r.h
}

type Concept

predicate {:axiom} ValidConcept(c: Concept)

function {:axiom} area(c: Concept): int32
  requires ValidConcept(c)
  ensures 0 <= area(c) <= 1_000_000

// Model<Square>
datatype ModelSquare = ModelSquare(value_: Square)

predicate ValidModelSquare(m: ModelSquare) { ValidSquare(m.value_) }

method MakeModelSquare(value: Square) returns (m: ModelSquare)
  requires ValidSquare(value)
  ensures ValidModelSquare(m)
{
  m := ModelSquare(value);
}

function model_square_area(m: ModelSquare): int32
  requires ValidModelSquare(m)
  ensures 0 <= model_square_area(m) <= 1_000_000 && model_square_area(m) == square_area(m.value_)
{
  square_area(m.value_)
}

function {:axiom} ModelSquareAsConcept(m: ModelSquare): Concept
  ensures ValidConcept(ModelSquareAsConcept(m)) == ValidModelSquare(m)
  ensures ValidModelSquare(m) ==> area(ModelSquareAsConcept(m)) == model_square_area(m)

// Model<Rect>
datatype ModelRect = ModelRect(value_: Rect)

predicate ValidModelRect(m: ModelRect) { ValidRect(m.value_) }

method MakeModelRect(value: Rect) returns (m: ModelRect)
  requires ValidRect(value)
  ensures ValidModelRect(m)
{
  m := ModelRect(value);
}

function model_rect_area(m: ModelRect): int32
  requires ValidModelRect(m)
  ensures 0 <= model_rect_area(m) <= 1_000_000 && model_rect_area(m) == rect_area(m.value_)
{
  rect_area(m.value_)
}

function {:axiom} ModelRectAsConcept(m: ModelRect): Concept
  ensures ValidConcept(ModelRectAsConcept(m)) == ValidModelRect(m)
  ensures ValidModelRect(m) ==> area(ModelRectAsConcept(m)) == model_rect_area(m)

// Shape and its constructor template at Square and at Rect
datatype Shape = Shape(self_: Option<Concept>)

predicate ValidShape(s: Shape) { s.self_.Some? && ValidConcept(s.self_.value) }

method MakeShapeSquare(value: Square) returns (s: Shape)
  requires ValidSquare(value)
  ensures ValidShape(s)
{
  var m := MakeModelSquare(value);
  s := Shape(Some(ModelSquareAsConcept(m)));
}

method MakeShapeRect(value: Rect) returns (s: Shape)
  requires ValidRect(value)
  ensures ValidShape(s)
{
  var m := MakeModelRect(value);
  s := Shape(Some(ModelRectAsConcept(m)));
}

function shape_area(s: Shape): int32
  requires ValidShape(s)
  ensures 0 <= shape_area(s) <= 1_000_000
{
  area(s.self_.value)
}

method two_shapes(side: int32, w: int32, h: int32) returns (result: int32)
  requires 0 <= side <= 1000 && 0 <= w <= 1000 && 0 <= h <= 1000
  ensures 0 <= result <= 2_000_000
{
  var a := MakeShapeSquare(Square(side));
  var b := MakeShapeRect(Rect(w, h));
  result := shape_area(a) + shape_area(b);
}
