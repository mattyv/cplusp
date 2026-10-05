// Each instantiation of the class template is its own datatype, decision 0029. The object is a value, a const method is a
// function over it, and a method that changes it takes it in and gives it back. Valid is a predicate every method keeps.
newtype int32 = x: int | -0x8000_0000 <= x < 0x8000_0000
newtype uint64 = x: int | 0 <= x < 0x1_0000_0000_0000_0000

datatype Stack32 = Stack32(items: seq<int32>, capacity: uint64)

predicate Valid32(s: Stack32) { s.capacity > 0 && |s.items| <= s.capacity as int }

function size32(s: Stack32): uint64 requires Valid32(s) { |s.items| as uint64 }

function top32(s: Stack32): int32 requires Valid32(s) && size32(s) > 0 { s.items[|s.items| - 1] }

method Make32(capacity: uint64) returns (s: Stack32)
  requires capacity > 0
  ensures Valid32(s) && size32(s) == 0 && s.capacity == capacity
{
  s := Stack32([], capacity);
}

method push32(s: Stack32, x: int32) returns (s': Stack32)
  requires Valid32(s) && size32(s) < s.capacity
  ensures Valid32(s') && s'.capacity == s.capacity && size32(s') == size32(s) + 1 && top32(s') == x
{
  s' := Stack32(s.items + [x], s.capacity);
}

method pop32(s: Stack32) returns (s': Stack32)
  requires Valid32(s) && size32(s) > 0
  ensures Valid32(s') && s'.capacity == s.capacity && size32(s') == size32(s) - 1
{
  s' := Stack32(s.items[..|s.items| - 1], s.capacity);
}

datatype Point = Point(x: int32, y: int32)

datatype StackPoint = StackPoint(items: seq<Point>, capacity: uint64)

predicate ValidPoint(s: StackPoint) { s.capacity > 0 && |s.items| <= s.capacity as int }

function sizePoint(s: StackPoint): uint64 requires ValidPoint(s) { |s.items| as uint64 }

function topPoint(s: StackPoint): Point requires ValidPoint(s) && sizePoint(s) > 0 { s.items[|s.items| - 1] }

method MakePoint(capacity: uint64) returns (s: StackPoint)
  requires capacity > 0
  ensures ValidPoint(s) && sizePoint(s) == 0 && s.capacity == capacity
{
  s := StackPoint([], capacity);
}

method pushPoint(s: StackPoint, p: Point) returns (s': StackPoint)
  requires ValidPoint(s) && sizePoint(s) < s.capacity
  ensures ValidPoint(s') && s'.capacity == s.capacity && sizePoint(s') == sizePoint(s) + 1 && topPoint(s') == p
{
  s' := StackPoint(s.items + [p], s.capacity);
}

method push_three() returns (result: int32)
  ensures result == 3
{
  var s := Make32(4);
  s := push32(s, 1);
  s := push32(s, 2);
  s := push32(s, 3);
  result := top32(s);
}

method last_point_y() returns (result: int32)
  ensures result == 7
{
  var s := MakePoint(2);
  s := pushPoint(s, Point(1, 2));
  s := pushPoint(s, Point(5, 7));
  result := topPoint(s).y;
}
