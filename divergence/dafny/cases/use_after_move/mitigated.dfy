// Model B: a move is a copy, and the source is gone. The source gets an unspecified value, so a read of it proves nothing.
// The model uses t only, as the fixed C++ does. Put `|s|` in place of `|t|` and the contract no longer verifies.
newtype uint8 = x: int | 0 <= x < 0x100
newtype uint64 = x: int | 0 <= x < 0x1_0000_0000_0000_0000

method total(s0: seq<uint8>) returns (result: uint64)
  requires |s0| < 0x8000_0000_0000_0000
  ensures result as int == 2 * |s0|
{
  var t := s0;
  var s: seq<uint8> :| true;
  var n := |t| as uint64;
  result := n + n;
}

// The model proves 4 for the two bytes of "hi", and so does the fixed C++. A vector of bytes is a seq<uint8>, decision 0031.
method Demo() {
  var r := total([0x68, 0x69]);
  assert r == 4;
}
