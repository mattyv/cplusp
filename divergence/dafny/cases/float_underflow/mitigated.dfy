// Model B: the product is `fmul`, and the contract is an error bound. The ETA term is the absolute error of a product below the normal range.
// It lets the result be 0 when the product is below the smallest subnormal. The model cannot prove the result is not 0.
include "../../Float.dfy"
import opened Float

method scaled(a: real, b: real) returns (result: real)
  requires abs(a * b) <= MAX
  ensures abs(result - a * b) <= EPS * abs(a * b) + ETA
{
  RoundError(a * b);
  result := fmul(a, b);
}

// The product of 1e-200 and 1e-200 is 1e-400. The bound on the result is the one the contract gives, and it is not an equality.
method Demo() {
  var r := scaled(1e-200, 1e-200);
  assert r <= (1.0 + EPS) / 1e400 + ETA;
}
