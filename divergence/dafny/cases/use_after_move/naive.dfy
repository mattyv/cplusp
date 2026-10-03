// Model A: `std::move(s)` is a copy, `var t := s`, and s stays what it was.
// The model reads s after the move and gets the full string. C++ leaves s valid but unspecified.
newtype uint64 = x: int | 0 <= x < 0x1_0000_0000_0000_0000

method total(s: seq<char>) returns (result: uint64)
  requires |s| < 0x8000_0000_0000_0000
  ensures result as int == 2 * |s|
{
  var t := s;
  result := (|s| + |t|) as uint64;
}

// The model proves 4 for "hi". In C++ the moved-from string is empty and the result is 2.
method Demo() {
  var r := total("hi");
  assert r == 4;
}
