// A loop carries an invariant and a decreases clause, and Dafny proves the contract from them. An early return is a return inside the
// loop. A switch is a match, and a match must cover every enumerator, as the C++ switch does. A vector has fewer than 2^64
// elements, since size() is a size_t, so the model may convert its length to uint64.
newtype int32 = x: int | -0x8000_0000 <= x < 0x8000_0000
newtype uint64 = x: int | 0 <= x < 0x1_0000_0000_0000_0000

method find(v: seq<int32>, target: int32) returns (result: uint64)
  requires |v| < 0x1_0000_0000_0000_0000
  ensures result as int <= |v|
  ensures result as int < |v| ==> v[result] == target
  ensures forall j :: 0 <= j < result as int ==> v[j] != target
{
  var i: uint64 := 0;
  while i as int < |v|
    invariant i as int <= |v|
    invariant forall j :: 0 <= j < i as int ==> v[j] != target
    decreases |v| - i as int
  {
    if v[i] == target {
      return i;
    }
    i := i + 1;
  }
  return |v| as uint64;
}

datatype Kind = Small | Large

method weight(k: Kind) returns (result: int32)
  ensures result == (if k == Small then 1 else 10)
{
  match k {
    case Small => result := 1;
    case Large => result := 10;
  }
}
