// Text is a seq<uint8>, a span of bytes, and the contract names each byte. Dafny has its own string type of characters from Unicode, and
// the C++ char is a different thing with no fixed width, so the model uses bytes and not the Dafny string. The loop invariant says that
// the bytes before i agree. The caller builds the four bytes of "GET " as a seq, and the proof of its contract comes from starts_with.
newtype uint8 = x: int | 0 <= x < 0x100
newtype uint64 = x: int | 0 <= x < 0x1_0000_0000_0000_0000

type Bytes = s: seq<uint8> | |s| < 0x1_0000_0000_0000_0000 witness []

method starts_with(text: Bytes, prefix: Bytes) returns (result: bool)
  ensures result == (|text| >= |prefix| && forall i :: 0 <= i < |prefix| ==> text[i] == prefix[i])
{
  if |prefix| > |text| {
    return false;
  }
  var i: uint64 := 0;
  while i as int < |prefix|
    invariant i as int <= |prefix|
    invariant forall j :: 0 <= j < i as int ==> text[j] == prefix[j]
    decreases |prefix| - i as int
  {
    if text[i] != prefix[i] {
      return false;
    }
    i := i + 1;
  }
  return true;
}

method is_get_request(line: Bytes) returns (result: bool)
  ensures result == (|line| >= 4 && line[0] == 0x47 && line[1] == 0x45 && line[2] == 0x54 && line[3] == 0x20)
{
  var get: Bytes := [0x47, 0x45, 0x54, 0x20];
  result := starts_with(line, get);
}
