// A non-const reference parameter is a value in and a value out, decision 0029. A value model cannot see two names for one
// object, so the C++ clause `requires &dst != &src` has no counterpart on values. The caller proves it, and the C++ contract is
// false for take(x, x), where the second line clears the value that the first line copied.
newtype int32 = x: int | -0x8000_0000 <= x < 0x8000_0000

method take(dst: int32, src: int32) returns (dst': int32, src': int32)
  ensures dst' == src && src' == 0
{
  dst' := src;
  src' := 0;
}
