// Model A: `n` is a local variable, set to 0 on every call. Every call returns 1, and the proof goes through.
// In the C++, `n` is static. It is set once, and every call adds 1 to the same object.
newtype int32 = x: int | -0x8000_0000 <= x < 0x8000_0000

method counter() returns (result: int32)
  ensures result == 1
{
  var n: int32 := 0;
  n := n + 1;
  result := n;
}
