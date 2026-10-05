// The interface is an opaque type, decision 0029, and the decorator holds the component it owns as an Option of that type, as a
// unique_ptr member is. The decorator is a datatype with its own contract on its own value, and the caller reads the bound of the
// decorator from that contract, not from the interface. The conversions to the interface say only what a const function reads, and
// are trusted, as the vtables are. A product of two bounded numbers is a nonlinear fact, so a lemma proves it. A move of a
// unique_ptr is a copy, and the source is not read again.
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

type Component

predicate {:axiom} ValidComponent(c: Component)

function {:axiom} cost(c: Component, x: int32): int32
  requires ValidComponent(c) && 0 <= x <= 1000
  ensures 0 <= cost(c, x) <= 1_000_000

datatype Linear = Linear(rate_: int32)

predicate ValidLinear(l: Linear) { 0 <= l.rate_ <= 1000 }

method MakeLinear(rate: int32) returns (l: Linear)
  requires 0 <= rate <= 1000
  ensures ValidLinear(l) && l.rate_ == rate
{
  l := Linear(rate);
}

function linear_cost(l: Linear, x: int32): int32
  requires ValidLinear(l) && 0 <= x <= 1000
  ensures 0 <= linear_cost(l, x) <= 1_000_000
  ensures linear_cost(l, x) == x * l.rate_
{
  ProductAtMost(x as int, l.rate_ as int);
  x * l.rate_
}

function {:axiom} LinearAsComponent(l: Linear): Component
  ensures ValidComponent(LinearAsComponent(l)) == ValidLinear(l)
  ensures ValidLinear(l) ==> forall x: int32 :: 0 <= x <= 1000 ==> cost(LinearAsComponent(l), x) == linear_cost(l, x)

datatype Capped = Capped(inner_: Option<Component>, limit_: int32)

predicate ValidCapped(c: Capped) { c.inner_.Some? && ValidComponent(c.inner_.value) && 0 <= c.limit_ <= 1_000_000 }

method MakeCapped(inner: Option<Component>, limit: int32) returns (c: Capped)
  requires inner.Some? && ValidComponent(inner.value) && 0 <= limit <= 1_000_000
  ensures ValidCapped(c) && c.limit_ == limit
{
  c := Capped(inner, limit);
}

function capped_cost(c: Capped, x: int32): int32
  requires ValidCapped(c) && 0 <= x <= 1000
  ensures capped_cost(c, x) == (if cost(c.inner_.value, x) < c.limit_ then cost(c.inner_.value, x) else c.limit_)
  ensures 0 <= capped_cost(c, x) <= c.limit_
{
  var inner_cost := cost(c.inner_.value, x);
  if inner_cost < c.limit_ then inner_cost else c.limit_
}

function {:axiom} CappedAsComponent(c: Capped): Component
  ensures ValidComponent(CappedAsComponent(c)) == ValidCapped(c)
  ensures ValidCapped(c) ==> forall x: int32 :: 0 <= x <= 1000 ==> cost(CappedAsComponent(c), x) == capped_cost(c, x)

method quote(x: int32) returns (result: int32)
  requires 0 <= x <= 1000
  ensures 0 <= result <= 300
{
  var rate := MakeLinear(10);
  var base: Option<Component> := Some(LinearAsComponent(rate));
  var inner := MakeCapped(base, 500);
  var mid: Option<Component> := Some(CappedAsComponent(inner));
  var outer := MakeCapped(mid, 300);
  result := capped_cost(outer, x);
}
