// Model B: the conversion truncates toward zero, and the contract requires that the value fits.
// A double is a real here, and no rounding takes place, so the model does not need Double.dfy.
newtype int32 = x: int | -0x8000_0000 <= x < 0x8000_0000

function trunc(x: real): int { if x >= 0.0 then x.Floor else -((-x).Floor) }

lemma Demo()
  ensures trunc(-3.7) == -3 && trunc(3.7) == 3
{}

method whole(x: real) returns (result: int32)
  requires -2147483649.0 < x < 2147483648.0
  ensures result as int == trunc(x)
{
  result := trunc(x) as int32;
}
