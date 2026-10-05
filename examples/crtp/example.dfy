// A class template has no model, decision 0029. Each Step it is used at gets its own datatype and its own functions: TwiceNegate and
// TwiceCap for Twice<Step>. The member is a value, so the template holds its step as a field. There is no base class and no cast,
// and so nothing to model but the calls.
newtype int32 = x: int | -0x8000_0000 <= x < 0x8000_0000

datatype Negate = Negate

predicate ValidNegate(n: Negate) { true }

function negate_apply(n: Negate, x: int32): int32
  requires ValidNegate(n) && -1_000_000 <= x <= 1_000_000
  ensures negate_apply(n, x) == -x && -1_000_000 <= negate_apply(n, x) <= 1_000_000
{
  -x
}

datatype Cap = Cap(limit_: int32)

predicate ValidCap(c: Cap) { -1_000_000 <= c.limit_ <= 1_000_000 }

method MakeCap(limit: int32) returns (c: Cap)
  requires -1_000_000 <= limit <= 1_000_000
  ensures ValidCap(c) && c.limit_ == limit
{
  c := Cap(limit);
}

function cap_apply(c: Cap, x: int32): int32
  requires ValidCap(c) && -1_000_000 <= x <= 1_000_000
  ensures cap_apply(c, x) == (if x < c.limit_ then x else c.limit_) && -1_000_000 <= cap_apply(c, x) <= 1_000_000
{
  if x < c.limit_ then x else c.limit_
}

// Twice<Negate>
datatype TwiceNegate = TwiceNegate(step_: Negate)

predicate ValidTwiceNegate(t: TwiceNegate) { ValidNegate(t.step_) }

method MakeTwiceNegate(step: Negate) returns (t: TwiceNegate)
  requires ValidNegate(step)
  ensures ValidTwiceNegate(t) && t.step_ == step
{
  t := TwiceNegate(step);
}

function twice_negate_run(t: TwiceNegate, x: int32): int32
  requires ValidTwiceNegate(t) && -1_000_000 <= x <= 1_000_000
  ensures twice_negate_run(t, x) == negate_apply(t.step_, negate_apply(t.step_, x)) && -1_000_000 <= twice_negate_run(t, x) <= 1_000_000
{
  negate_apply(t.step_, negate_apply(t.step_, x))
}

// Twice<Cap>
datatype TwiceCap = TwiceCap(step_: Cap)

predicate ValidTwiceCap(t: TwiceCap) { ValidCap(t.step_) }

method MakeTwiceCap(step: Cap) returns (t: TwiceCap)
  requires ValidCap(step)
  ensures ValidTwiceCap(t) && t.step_ == step
{
  t := TwiceCap(step);
}

function twice_cap_run(t: TwiceCap, x: int32): int32
  requires ValidTwiceCap(t) && -1_000_000 <= x <= 1_000_000
  ensures twice_cap_run(t, x) == cap_apply(t.step_, cap_apply(t.step_, x)) && -1_000_000 <= twice_cap_run(t, x) <= 1_000_000
{
  cap_apply(t.step_, cap_apply(t.step_, x))
}

method negate_twice(x: int32) returns (result: int32)
  requires -1_000_000 <= x <= 1_000_000
  ensures result == x
{
  var t := MakeTwiceNegate(Negate);
  result := twice_negate_run(t, x);
}

method cap_twice(x: int32) returns (result: int32)
  requires -1_000_000 <= x <= 1_000_000
  ensures result == (if x < 5 then x else 5)
{
  var c := MakeCap(5);
  var t := MakeTwiceCap(c);
  result := twice_cap_run(t, x);
}
