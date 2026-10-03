// Model B: the same file as model A. The model still cannot see a destructor.
// The rule lives in the gate and in the C++: Base has `virtual ~Base() = default;`, so the delete is defined.
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
