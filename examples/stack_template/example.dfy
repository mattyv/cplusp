// Each instantiation of the class template is its own Dafny class. The members are the state, so a method that
// changes one has `modifies this`. The invariant of the class is a predicate every method keeps.
newtype int32 = x: int | -0x8000_0000 <= x < 0x8000_0000
newtype uint64 = x: int | 0 <= x < 0x1_0000_0000_0000_0000

class Stack32 {
  var items: seq<int32>
  var capacity: uint64

  ghost predicate Valid()
    reads this
  {
    capacity > 0 && |items| <= capacity as int
  }

  constructor (capacity: uint64)
    requires capacity > 0
    ensures Valid() && |items| == 0 && this.capacity == capacity
  {
    items := [];
    this.capacity := capacity;
  }

  function size(): uint64
    reads this
    requires Valid()
  {
    |items| as uint64
  }

  method push(x: int32)
    requires Valid() && size() < capacity
    modifies this
    ensures Valid() && capacity == old(capacity) && size() == old(size()) + 1 && top() == x
  {
    items := items + [x];
  }

  function top(): int32
    reads this
    requires Valid() && size() > 0
  {
    items[|items| - 1]
  }

  method pop()
    requires Valid() && size() > 0
    modifies this
    ensures Valid() && capacity == old(capacity) && size() == old(size()) - 1
  {
    items := items[..|items| - 1];
  }
}

datatype Point = Point(x: int32, y: int32)

class StackPoint {
  var items: seq<Point>
  var capacity: uint64

  ghost predicate Valid()
    reads this
  {
    capacity > 0 && |items| <= capacity as int
  }

  constructor (capacity: uint64)
    requires capacity > 0
    ensures Valid() && |items| == 0 && this.capacity == capacity
  {
    items := [];
    this.capacity := capacity;
  }

  function size(): uint64 reads this requires Valid() { |items| as uint64 }

  method push(p: Point)
    requires Valid() && size() < capacity
    modifies this
    ensures Valid() && capacity == old(capacity) && size() == old(size()) + 1 && top() == p
  {
    items := items + [p];
  }

  function top(): Point reads this requires Valid() && size() > 0 { items[|items| - 1] }
}

method push_three() returns (result: int32)
  ensures result == 3
{
  var s := new Stack32(4);
  s.push(1);
  s.push(2);
  s.push(3);
  result := s.top();
}

method last_point_y() returns (result: int32)
  ensures result == 7
{
  var s := new StackPoint(2);
  s.push(Point(1, 2));
  s.push(Point(5, 7));
  result := s.top().y;
}
