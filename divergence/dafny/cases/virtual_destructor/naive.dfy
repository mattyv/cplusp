// Model A: Base is a trait, Derived extends it, and the owner of the object is a plain reference.
// Dafny has no destructor and no delete, so the model has nothing to say about how the object dies. It verifies.
// In C++ the delete goes through Base, which has no virtual destructor, and that is undefined.
newtype int32 = x: int | -0x8000_0000 <= x < 0x8000_0000

trait Base {
  function value(): int32
}

class Derived extends Base {
  function value(): int32 { 2 }
}

method value_of_new() returns (result: int32)
  ensures result == 2
{
  var p: Base := new Derived;
  result := p.value();
}
