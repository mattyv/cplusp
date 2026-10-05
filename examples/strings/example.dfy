// Text is a seq<uint8>, a span of bytes, and the contract names each byte. Dafny has its own string type of characters from Unicode, and
// the C++ char is a different thing with no fixed width, so the model uses bytes and not the Dafny string. The loop invariant says that
// the bytes before i agree. The caller builds the four bytes of "GET " as a seq, and the proof of its contract comes from starts_with.
newtype int32 = x: int | -0x8000_0000 <= x < 0x8000_0000
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

// A trusted function is a method with no body, an axiom that states its contract. The body in trusted.cpp holds the std::string, and the
// model has no text type, so the contract is all the prover knows. The caller proves its contract from the three facts about the width.
method {:axiom} decimal_width(n: int32) returns (result: uint64)
  ensures 1 <= result <= 11
  ensures 0 <= n < 10 ==> result == 1
  ensures 10 <= n < 100 ==> result == 2

method position_width(row: int32, col: int32) returns (result: uint64)
  ensures 3 <= result <= 23
  ensures 0 <= row < 10 && 0 <= col < 10 ==> result == 3
{
  var row_width := decimal_width(row);
  var col_width := decimal_width(col);
  result := row_width + 1 + col_width;
}
