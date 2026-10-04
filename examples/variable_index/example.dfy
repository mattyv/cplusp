// A vector is a seq, and a vector passed by reference is an object that holds one. Every subscript needs a proof that
// the index is in range, and the contract carries it. The write is a seq update, and the frame says the other elements stay.
newtype int32 = x: int | -0x8000_0000 <= x < 0x8000_0000
newtype uint64 = x: int | 0 <= x < 0x1_0000_0000_0000_0000

class IntVec {
  var items: seq<int32>
}

method read_at(v: seq<int32>, i: uint64) returns (result: int32)
  requires i as int < |v|
  ensures result == v[i]
{
  result := v[i];
}

method write_at(v: IntVec, i: uint64, x: int32)
  requires i as int < |v.items|
  modifies v
  ensures |v.items| == |old(v.items)|
  ensures v.items[i] == x
  ensures forall j :: 0 <= j < |v.items| && j != i as int ==> v.items[j] == old(v.items[j])
{
  v.items := v.items[i as int := x];
}
