// Model B: the same model as A in its values. The model still cannot see a destructor, because it has no heap and no delete.
// The rule lives in the gate and in the C++: Base has `virtual ~Base() = default;`, so the delete is defined.
// Base is an opaque type, Derived is a datatype, and a unique_ptr to Base is an Option value, decision 0029.
newtype int32 = x: int | -0x8000_0000 <= x < 0x8000_0000

datatype Option<T> = None | Some(value: T)

type Base

function {:axiom} value(b: Base): int32

datatype Derived = Derived

function derived_value(d: Derived): int32 { 2 }

function {:axiom} AsBase(d: Derived): Base
  ensures value(AsBase(d)) == derived_value(d)

method value_of_new() returns (result: int32)
  ensures result == 2
{
  var p: Option<Base> := Some(AsBase(Derived));
  result := value(p.value);
}
