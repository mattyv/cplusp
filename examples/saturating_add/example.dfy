// The three cases of the contract are the three ensures, written on the exact integers with `as int`. The sum is taken in int64, as
// in the C++, and it cannot overflow there, so the model needs no precondition. The cast back to int32 follows the two tests, which
// leave the sum in range. clamp has the same contract as the C++, and the prover proves it from the two tests.
newtype int32 = x: int | -0x8000_0000 <= x < 0x8000_0000
newtype int64 = x: int | -0x8000_0000_0000_0000 <= x < 0x8000_0000_0000_0000

method saturating_add(a: int32, b: int32) returns (result: int32)
  ensures a as int + b as int > 0x7FFF_FFFF ==> result == 0x7FFF_FFFF
  ensures a as int + b as int < -0x8000_0000 ==> result == -0x8000_0000
  ensures -0x8000_0000 <= a as int + b as int <= 0x7FFF_FFFF ==> result as int == a as int + b as int
{
  var sum: int64 := (a as int64) + (b as int64);
  if sum > 0x7FFF_FFFF {
    return 0x7FFF_FFFF;
  }
  if sum < -0x8000_0000 {
    return -0x8000_0000;
  }
  return sum as int32;
}

method clamp(x: int32, lo: int32, hi: int32) returns (result: int32)
  requires lo <= hi
  ensures lo <= result <= hi
  ensures x < lo ==> result == lo
  ensures x > hi ==> result == hi
  ensures lo <= x <= hi ==> result == x
{
  if x < lo {
    return lo;
  }
  if x > hi {
    return hi;
  }
  return x;
}

method successor(x: int32) returns (result: int32)
  ensures result >= x && (x < 0x7FFF_FFFF ==> result as int == x as int + 1)
{
  result := saturating_add(x, 1);
}
