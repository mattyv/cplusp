// Model B: the C++ binds a reference, `const Base& b = d;`, so b is the same object as d and keeps its class.
// The same text as model A is exact for a reference. It was wrong for the copy.
newtype int32 = x: int | -0x8000_0000 <= x < 0x8000_0000

trait Base {
  function value(): int32
}

class Derived extends Base {
  function value(): int32 { 2 }
}

method value_of(d: Derived) returns (result: int32)
  ensures result == d.value()
{
  var b: Base := d;
  result := b.value();
}

// The model proves 2, and so does C++.
method Demo() {
  var d := new Derived;
  var r := value_of(d);
  assert r == 2;
}
