// A vector is a seq, and a vector passed by reference is a seq in and a seq out, decision 0029. Every subscript needs a proof that
// the index is in range, and the contract carries it. The write is a seq update, and the frame says the other elements stay.
newtype int32 = x: int | -0x8000_0000 <= x < 0x8000_0000
newtype uint64 = x: int | 0 <= x < 0x1_0000_0000_0000_0000

method read_at(v: seq<int32>, i: uint64) returns (result: int32)
  requires i as int < |v|
  ensures result == v[i]
{
  result := v[i];
}

method write_at(v: seq<int32>, i: uint64, x: int32) returns (v': seq<int32>)
  requires i as int < |v|
  ensures |v'| == |v|
  ensures v'[i] == x
  ensures forall j :: 0 <= j < |v'| ==> (j != i as int ==> v'[j] == v[j])
{
  v' := v[i as int := x];
}
