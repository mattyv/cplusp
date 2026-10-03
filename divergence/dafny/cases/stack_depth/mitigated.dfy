// Model B: the contract bounds the depth, `requires n <= 100000`, a bound the target holds.
// Dafny then refuses a call with a larger n, so `depth(10_000_000)` no longer verifies.
newtype int32 = x: int | -0x8000_0000 <= x < 0x8000_0000

method depth(n: int32) returns (result: int32)
  requires 0 <= n <= 100000
  decreases n
  ensures result == n
{
  if n == 0 {
    result := 0;
  } else {
    var r := depth(n - 1);
    result := 1 + r;
  }
}

// The model proves 100000, and the target holds that depth.
method Demo() {
  var r := depth(100_000);
  assert r == 100_000;
}
