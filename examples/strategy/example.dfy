// The interface is an opaque type, decision 0029, and its contract is the only thing the context knows. A const method is a function
// of the value, so two calls with the same strategy and the same argument give the same answer, and the context states it. Each class
// proves its own contract on its own datatype. The conversions to the interface say only what the const function reads, and are
// trusted, as the vtables are. A product of two bounded numbers is a nonlinear fact, so a lemma proves it.
newtype int32 = x: int | -0x8000_0000 <= x < 0x8000_0000

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

type Strategy

predicate {:axiom} Valid(s: Strategy)

function {:axiom} apply(s: Strategy, x: int32): int32
  requires Valid(s) && 0 <= x <= 1000
  ensures 0 <= apply(s, x) <= 1_000_000

datatype Squared = Squared

predicate ValidSquared(q: Squared) { true }

function squared_apply(q: Squared, x: int32): int32
  requires ValidSquared(q) && 0 <= x <= 1000
  ensures 0 <= squared_apply(q, x) <= 1_000_000
  ensures squared_apply(q, x) == x * x
{
  ProductAtMost(x as int, x as int);
  x * x
}

datatype Scaled = Scaled(k: int32)

predicate ValidScaled(c: Scaled) { 0 <= c.k <= 1000 }

method MakeScaled(k: int32) returns (c: Scaled)
  requires 0 <= k <= 1000
  ensures ValidScaled(c) && c.k == k
{
  c := Scaled(k);
}

function scaled_apply(c: Scaled, x: int32): int32
  requires ValidScaled(c) && 0 <= x <= 1000
  ensures 0 <= scaled_apply(c, x) <= 1_000_000
  ensures scaled_apply(c, x) == x * c.k
{
  ProductAtMost(x as int, c.k as int);
  x * c.k
}

function {:axiom} SquaredAsStrategy(q: Squared): Strategy
  ensures Valid(SquaredAsStrategy(q)) == ValidSquared(q)
  ensures ValidSquared(q) ==> forall x: int32 :: 0 <= x <= 1000 ==> apply(SquaredAsStrategy(q), x) == squared_apply(q, x)

function {:axiom} ScaledAsStrategy(c: Scaled): Strategy
  ensures Valid(ScaledAsStrategy(c)) == ValidScaled(c)
  ensures ValidScaled(c) ==> forall x: int32 :: 0 <= x <= 1000 ==> apply(ScaledAsStrategy(c), x) == scaled_apply(c, x)

method apply_to_neighbours(s: Strategy, x: int32) returns (result: int32)
  requires Valid(s) && 0 <= x < 1000
  ensures 0 <= result <= 2_000_000 && result as int == apply(s, x) as int + apply(s, x + 1) as int
{
  result := apply(s, x) + apply(s, x + 1);
}

method demo() returns (result: int32)
  ensures result == 68
{
  var sq := Squared;
  var sc := MakeScaled(3);
  var a := apply_to_neighbours(SquaredAsStrategy(sq), 4);
  var b := apply_to_neighbours(ScaledAsStrategy(sc), 4);
  result := a + b;
}
