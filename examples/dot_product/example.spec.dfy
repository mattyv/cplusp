// Dot is the specification, the sum of the products. The lemmas give the bound on one product, since Dafny does not prove
// nonlinear bounds by itself.
function Dot(a: seq<int32>, b: seq<int32>): int
  requires |a| == |b|
  decreases |a|
{
  if |a| == 0 then 0 else Dot(a[..|a| - 1], b[..|b| - 1]) + a[|a| - 1] as int * b[|b| - 1] as int
}

lemma NonnegProduct(a: int, b: int)
  requires a >= 0 && b >= 0
  ensures a * b >= 0
  decreases a
{
  if a > 0 {
    NonnegProduct(a - 1, b);
  }
}

lemma ProductBoundNonneg(a: int, b: int)
  requires 0 <= a <= 1_000_000 && 0 <= b <= 1_000_000
  ensures 0 <= a * b <= 1_000_000_000_000
{
  NonnegProduct(a, b);
  NonnegProduct(1_000_000 - a, 1_000_000);
  NonnegProduct(a, 1_000_000 - b);
}

lemma ProductBound(x: int, y: int)
  requires -1_000_000 <= x <= 1_000_000 && -1_000_000 <= y <= 1_000_000
  ensures -1_000_000_000_000 <= x * y <= 1_000_000_000_000
{
  var ax := if x < 0 then -x else x;
  var ay := if y < 0 then -y else y;
  ProductBoundNonneg(ax, ay);
  assert x * y == ax * ay || x * y == -(ax * ay);
}
