// Sum is the specification, the sum of the bytes with no modulus. The accumulator is a uint32 that the step keeps below 256, so
// `acc + byte` is at most 510 and the modulus is exact. A span is a seq shorter than 2^64, as in binary_search. The two asserts in the
// loop show Dafny that the prefix of the next length ends in the byte just read.
newtype uint8 = x: int | 0 <= x < 0x100
newtype uint32 = x: int | 0 <= x < 0x1_0000_0000
newtype uint64 = x: int | 0 <= x < 0x1_0000_0000_0000_0000

type Span = s: seq<uint8> | |s| < 0x1_0000_0000_0000_0000 witness []

function Sum(s: seq<uint8>): int
  decreases |s|
{
  if |s| == 0 then 0 else Sum(s[..|s| - 1]) + s[|s| - 1] as int
}

lemma SumNonneg(s: seq<uint8>)
  ensures Sum(s) >= 0
  decreases |s|
{
  if |s| > 0 {
    SumNonneg(s[..|s| - 1]);
  }
}

method checksum(bytes: Span) returns (result: uint8)
  ensures result as int == Sum(bytes) % 256
{
  var acc: uint32 := 0;
  var i: uint64 := 0;
  while i as int < |bytes|
    invariant i as int <= |bytes|
    invariant acc as int == Sum(bytes[..i]) % 256
    decreases |bytes| - i as int
  {
    assert bytes[..i + 1][..i] == bytes[..i];
    assert bytes[..i + 1][i] == bytes[i];
    SumNonneg(bytes[..i]);
    acc := (acc + bytes[i] as uint32) % 256;
    i := i + 1;
  }
  assert bytes[..i] == bytes;
  result := acc as uint8;
}

method matches(bytes: Span, expected: uint8) returns (result: bool)
  ensures result == (Sum(bytes) % 256 == expected as int)
{
  var c := checksum(bytes);
  result := c == expected;
}
