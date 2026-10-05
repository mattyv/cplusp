// The interface is a trait, and its contract is the promise of every implementation. The invariant of the C++ classes is the predicate
// Valid(), which the constructors establish. The trait cannot know the fields, so the model states Valid() as a requirement on each shape.
// A vector of unique_ptr is a seq of nullable references, and a null test is a requirement. The sum proves from the trait contract alone.
// A product of two bounded numbers is a nonlinear fact, so a lemma proves it.
newtype int32 = x: int | -0x8000_0000 <= x < 0x8000_0000
newtype int64 = x: int | -0x8000_0000_0000_0000 <= x < 0x8000_0000_0000_0000

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

trait Shape {
  ghost predicate Valid()
    reads this

  function area(): int32
    reads this
    requires Valid()
    ensures 0 <= area() <= 1_000_000
}

class Square extends Shape {
  var side: int32

  ghost predicate Valid()
    reads this
  {
    0 <= side <= 1000
  }

  constructor (side: int32)
    requires 0 <= side <= 1000
    ensures Valid() && this.side == side
  {
    this.side := side;
  }

  function area(): int32
    reads this
    requires Valid()
    ensures area() == side * side
  {
    ProductAtMost(side as int, side as int);
    side * side
  }
}

class Rect extends Shape {
  var w: int32
  var h: int32

  ghost predicate Valid()
    reads this
  {
    0 <= w <= 1000 && 0 <= h <= 1000
  }

  constructor (w: int32, h: int32)
    requires 0 <= w <= 1000 && 0 <= h <= 1000
    ensures Valid() && this.w == w && this.h == h
  {
    this.w := w;
    this.h := h;
  }

  function area(): int32
    reads this
    requires Valid()
    ensures area() == w * h
  {
    ProductAtMost(w as int, h as int);
    w * h
  }
}

method total_area(shapes: seq<Shape?>) returns (result: int64)
  requires |shapes| <= 1000
  requires forall i :: 0 <= i < |shapes| ==> shapes[i] != null
  requires forall i :: 0 <= i < |shapes| ==> shapes[i].Valid()
  ensures 0 <= result <= 1_000_000_000
{
  var total: int64 := 0;
  var i := 0;
  while i < |shapes|
    invariant 0 <= i <= |shapes|
    invariant 0 <= total as int <= 1_000_000 * i
    decreases |shapes| - i
  {
    var a := shapes[i].area();
    total := total + (a as int64);
    i := i + 1;
  }
  result := total;
}

method sample_total() returns (result: int64)
  ensures 0 <= result <= 1_000_000_000
{
  var sq := new Square(5);
  var r := new Rect(2, 3);
  var shapes: seq<Shape?> := [sq, r];
  result := total_area(shapes);
}
