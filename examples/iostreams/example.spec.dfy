// The quotient is at most 100: the numerator is at most 100 * w, and division by a positive w keeps the order. Dafny does not
// prove a nonlinear fact by itself, so the lemma states it, with the three steps of example.dfy.
lemma DivBound(p: int, w: int)
  requires 0 <= p <= w && 0 < w
  ensures 0 <= (p * 100) / w <= 100
{
  assert p * 100 <= w * 100;
  assert (w * 100) / w == 100;
  assert (p * 100) / w <= (w * 100) / w;
}
