// A std::array<int32_t, 8> is a seq of length 8, and the object is a datatype value, decision 0029. Valid keeps the length and the
// count. The method push gives the vector back and says whether it took the element. The capacity is the number 8, as in the C++.
newtype int32 = x: int | -0x8000_0000 <= x < 0x8000_0000
newtype uint64 = x: int | 0 <= x < 0x1_0000_0000_0000_0000

datatype Small = Small(items: seq<int32>, count: uint64)

predicate Valid(s: Small) { |s.items| == 8 && s.count <= 8 }

function size(s: Small): uint64 requires Valid(s) { s.count }

function at(s: Small, i: uint64): int32
  requires Valid(s) && i < s.count
{
  s.items[i]
}

method Make() returns (s: Small)
  ensures Valid(s) && size(s) == 0
{
  s := Small([0, 0, 0, 0, 0, 0, 0, 0], 0);
}

method push(s: Small, x: int32) returns (s': Small, result: bool)
  requires Valid(s)
  ensures Valid(s') && result == (size(s) < 8)
  ensures size(s') == (if result then size(s) + 1 else size(s))
  ensures result ==> at(s', size(s') - 1) == x
  ensures forall i :: 0 <= i < size(s) ==> at(s', i) == at(s, i)
{
  if s.count == 8 {
    return s, false;
  }
  return Small(s.items[s.count := x], s.count + 1), true;
}

method ninth_push_is_refused() returns (result: bool)
  ensures result == false
{
  var v := Make();
  var i: int32 := 0;
  while i < 8
    invariant 0 <= i <= 8 && Valid(v) && size(v) == i as uint64
    decreases 8 - i
  {
    var accepted: bool;
    v, accepted := push(v, i);
    i := i + 1;
  }
  var accepted: bool;
  v, accepted := push(v, 8);
  result := accepted;
}

method sum_of_two() returns (result: int32)
  ensures result == 7
{
  var v := Make();
  var ok: bool;
  v, ok := push(v, 3);
  v, ok := push(v, 4);
  result := at(v, 0) + at(v, 1);
}
