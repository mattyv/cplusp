// Model A: Base is a trait, Derived extends it, and the constructor body of Base is a method on the object.
// `kind()` inside it dispatches on the class of the object, so it goes to Derived.
// C++ dispatches to the class under construction, which is Base.
newtype int32 = x: int | -0x8000_0000 <= x < 0x8000_0000

trait Base {
  var seen: int32
  function kind(): int32

  method init()
    modifies this
    ensures seen == kind()
  {
    seen := kind();
  }
}

class Derived extends Base {
  function kind(): int32 { 2 }
}

method seen_kind() returns (result: int32)
  ensures result == 2
{
  var d := new Derived;
  d.init();
  result := d.seen;
}
