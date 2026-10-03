// Model B: no virtual call in a constructor. The caller sets `seen` after construction,
// when the object has its final class, and `kind()` goes to Derived in C++ and in the model.
newtype int32 = x: int | -0x8000_0000 <= x < 0x8000_0000

trait Base {
  var seen: int32
  function kind(): int32
}

class Derived extends Base {
  function kind(): int32 { 2 }
}

method seen_kind() returns (result: int32)
  ensures result == 2
{
  var d := new Derived;
  d.seen := d.kind();
  result := d.seen;
}
