// Model A: the recursion ends, because n goes down to 0, and the result is n. Dafny proves it for every n.
// It proves `depth(10_000_000) == 10_000_000`. The program overflows its stack long before.
newtype int32 = x: int | -0x8000_0000 <= x < 0x8000_0000

method depth(n: int32) returns (result: int32)
  requires n >= 0
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

// The model proves 10000000. In C++ the stack overflows.
method Demo() {
  var r := depth(10_000_000);
  assert r == 10_000_000;
}
