// Two spans are two seqs of the same length. Dot is the specification, the sum of the products. Each product is at most 10^12 in
// magnitude, so after i steps the sum is at most 10^12 * i. With a million elements that is inside int64. The lemmas give the
// bound on one product, since Dafny does not prove nonlinear bounds by itself.
newtype int32 = x: int | -0x8000_0000 <= x < 0x8000_0000
newtype int64 = x: int | -0x8000_0000_0000_0000 <= x < 0x8000_0000_0000_0000

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

method dot(a: seq<int32>, b: seq<int32>) returns (result: int64)
  requires |a| == |b| && |a| <= 1_000_000
  requires forall i :: 0 <= i < |a| ==> -1_000_000 <= a[i] <= 1_000_000
  requires forall i :: 0 <= i < |b| ==> -1_000_000 <= b[i] <= 1_000_000
  ensures result as int == Dot(a, b)
{
  var acc: int64 := 0;
  var i := 0;
  while i < |a|
    invariant 0 <= i <= |a|
    invariant acc as int == Dot(a[..i], b[..i])
    invariant -1_000_000_000_000 * i <= acc as int <= 1_000_000_000_000 * i
    decreases |a| - i
  {
    ProductBound(a[i] as int, b[i] as int);
    assert a[..i + 1][..i] == a[..i];
    assert b[..i + 1][..i] == b[..i];
    acc := acc + (a[i] as int64) * (b[i] as int64);
    i := i + 1;
  }
  assert a[..i] == a && b[..i] == b;
  result := acc;
}
