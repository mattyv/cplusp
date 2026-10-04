// A class is a Dafny class. The C++ invariant is a predicate Valid(), which the constructor establishes and each method
// keeps. `modifies this` in the C++ contract is `modifies this` here. A local object is a new object.
newtype int32 = x: int | -0x8000_0000 <= x < 0x8000_0000

class Counter {
  var n: int32

  predicate Valid()
    reads this
  {
    0 <= n <= 1000
  }

  constructor (start: int32)
    requires 0 <= start <= 1000
    ensures Valid() && value() == start
  {
    n := start;
  }

  function value(): int32
    reads this
  {
    n
  }

  method bump()
    requires Valid() && value() < 1000
    modifies this
    ensures Valid() && value() == old(value()) + 1
  {
    n := n + 1;
  }
}

method bumped_twice(start: int32) returns (result: int32)
  requires 0 <= start <= 998
  ensures result == start + 2
{
  var c := new Counter(start);
  c.bump();
  c.bump();
  result := c.value();
}
