// A span of bytes is a seq<uint8>, and the optional is a datatype, as in parse_digits. The sum of the bytes is taken in int32, as the C++
// does after promotion, and then it is a uint16. It is at most 65535, so Dafny proves the conversion. The field kind is named as in the
// C++, since type is a keyword in Dafny.
newtype int32 = x: int | -0x8000_0000 <= x < 0x8000_0000
newtype uint8 = x: int | 0 <= x < 0x100
newtype uint16 = x: int | 0 <= x < 0x1_0000

datatype Option<T> = None | Some(value: T)

datatype Header = Header(version: uint8, length: uint16, kind: uint8)

method parse_header(bytes: seq<uint8>) returns (result: Option<Header>)
  ensures result.Some? == (|bytes| >= 4)
  ensures result.Some? ==> result.value.version == bytes[0] && result.value.kind == bytes[3]
  ensures result.Some? ==> result.value.length as int == bytes[1] as int + 256 * bytes[2] as int
{
  if |bytes| < 4 {
    return None;
  }
  var length := (bytes[1] as int32 + 256 * (bytes[2] as int32)) as uint16;
  return Some(Header(bytes[0], length, bytes[3]));
}

method frame_complete(bytes: seq<uint8>) returns (result: bool)
  ensures result == (|bytes| >= 4 && |bytes| - 4 >= bytes[1] as int + 256 * bytes[2] as int)
{
  var h := parse_header(bytes);
  if !h.Some? {
    return false;
  }
  return |bytes| - 4 >= h.value.length as int;
}
