// Model B: the search is over bytes, decision 0031, and it returns an Option<nat>. None is "no match", and there is no npos to do
// arithmetic on. The postcondition says what the C++ does in both cases. A text is a seq<uint8>, and 'z' is the byte 0x7A.
newtype uint8 = x: int | 0 <= x < 0x100
newtype uint64 = x: int | 0 <= x < 0x1_0000_0000_0000_0000

datatype Option<T> = None | Some(value: T)

const Z: uint8 := 0x7A

function Find(s: seq<uint8>, c: uint8): (r: Option<nat>)
  ensures r.Some? ==> r.value < |s| && s[r.value] == c
  ensures r.None? ==> forall i :: 0 <= i < |s| ==> s[i] != c
  decreases |s|
{
  if |s| == 0 then None
  else if s[0] == c then Some(0)
  else match Find(s[1..], c) {
    case Some(i) => Some(i + 1)
    case None => None
  }
}

method after(s: seq<uint8>) returns (result: uint64)
  requires |s| < 0x1_0000_0000_0000_0000
  ensures Find(s, Z).Some? ==> result as int == Find(s, Z).value + 1
  ensures Find(s, Z).None? ==> result == 0
{
  match Find(s, Z) {
    case Some(i) => result := (i + 1) as uint64;
    case None => result := 0;
  }
}

// The witness text is the three bytes of "abc". It has no 'z', so the result is 0, and so is the output of the fixed C++.
method after_z() returns (result: uint64)
  ensures result == 0
{
  result := after([0x61, 0x62, 0x63]);
}
