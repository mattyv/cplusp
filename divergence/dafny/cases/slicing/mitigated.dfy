// Model B: the C++ passes `d` to a reference parameter of type `const Base&`, so the callee sees the same object and its class.
// Base is an opaque type, decision 0029, and Derived is a datatype that meets the contract of Base. The conversion from a Derived
// to a Base view is trusted, as in interface_dispatch. A copy `Base b = d;` would make a separate Base value, and the gate refuses it.
newtype int32 = x: int | -0x8000_0000 <= x < 0x8000_0000

type Base

function {:axiom} value(b: Base): int32

datatype Derived = Derived

function derived_value(d: Derived): int32 { 2 }

function {:axiom} AsBase(d: Derived): Base
  ensures value(AsBase(d)) == derived_value(d)

method value_through_base(b: Base) returns (result: int32)
  ensures result == value(b)
{
  result := value(b);
}

method value_of(d: Derived) returns (result: int32)
  ensures result == derived_value(d)
{
  result := value_through_base(AsBase(d));
}

// The model proves 2, and so does C++.
method Demo() {
  var r := value_of(Derived);
  assert r == 2;
}
