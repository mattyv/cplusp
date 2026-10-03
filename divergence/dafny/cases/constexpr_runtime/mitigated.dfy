// Model B: `constexpr` changes nothing, so the contract is the one of any function.
// The precondition keeps the product in range, and every caller carries it, at run time as well as at compile time.
newtype int32 = x: int | -0x8000_0000 <= x < 0x8000_0000

// The prover needs help with a product of two unknowns. 46340 * 46340 is the largest square that fits.
lemma MulLe(a: int, b: int, c: nat)
  requires a <= b
  ensures a * c <= b * c
{
  if c > 0 {
    MulLe(a, b, c - 1);
  }
}

lemma SquareFits(x: int)
  requires -46340 <= x <= 46340
  ensures x * x <= 46340 * 46340
{
  var a := if x < 0 then -x else x;
  MulLe(a, 46340, a);
  assert a * a == x * x;
  assert 46340 * a <= 46340 * 46340;
}

method square(x: int32) returns (result: int32)
  requires -46340 <= x <= 46340
  ensures result as int == (x as int) * (x as int)
{
  SquareFits(x as int);
  result := x * x;
}
