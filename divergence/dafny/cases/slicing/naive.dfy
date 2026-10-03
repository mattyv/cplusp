// Model A: Base is a trait, Derived is a class that extends it, and a call dispatches on the class of the object.
// `var b: Base := d` keeps the object, so `b.value()` goes to Derived. C++ copies the Base part of d only.
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

// The model proves 2. In C++ the copy is a Base, and the result is 1.
method Demo() {
  var d := new Derived;
  var r := value_of(d);
  assert r == 2;
}
