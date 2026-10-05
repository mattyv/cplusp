// A class that gives out its size and the element at an index is a datatype over a seq, decision 0029, and size and at are functions
// of the value, since the C++ members are const. The walk is a loop by index, and its invariant says what the loop knows about the
// elements before i. A vector never holds 2^64 elements, so the seq type says so, and the size is a uint64 with no proof needed.
newtype int32 = x: int | -0x8000_0000 <= x < 0x8000_0000
newtype uint64 = x: int | 0 <= x < 0x1_0000_0000_0000_0000

type Items = s: seq<int32> | |s| < 0x1_0000_0000_0000_0000 witness []

datatype Series = Series(items_: Items)

function size(s: Series): uint64 { |s.items_| as uint64 }

function at(s: Series, i: uint64): int32
  requires i < size(s)
{
  s.items_[i]
}

method MakeSeries(items: Items) returns (s: Series)
  ensures size(s) as int == |items| && forall i: uint64 :: i < size(s) ==> at(s, i) == items[i]
{
  s := Series(items);
}

method largest(s: Series) returns (result: int32)
  requires size(s) > 0
  ensures exists i: uint64 :: i < size(s) && at(s, i) == result
  ensures forall i: uint64 :: i < size(s) ==> at(s, i) <= result
{
  var m := at(s, 0);
  var i: uint64 := 1;
  while i < size(s)
    invariant 1 <= i <= size(s)
    invariant exists j: uint64 :: j < i && at(s, j) == m
    invariant forall j: uint64 :: j < i ==> at(s, j) <= m
    decreases size(s) - i
  {
    if at(s, i) > m {
      m := at(s, i);
    }
    i := i + 1;
  }
  result := m;
}

method demo() returns (result: int32)
  ensures result == 9
{
  var items: Items := [3, 9, 4];
  var s := MakeSeries(items);
  result := largest(s);
  // The contract of largest gives an index that holds the result. The seq has three elements, so the index is one of three.
  var k: uint64 :| k < size(s) && at(s, k) == result;
  assert size(s) == 3 && at(s, 0) == 3 && at(s, 1) == 9 && at(s, 2) == 4;
  assert at(s, 1) <= result;
}
