// Model B: no virtual call in a constructor. A constructor builds a value, decision 0029, and a call on it is a call on the
// finished value. The caller sets `seen` after construction, when the object has its final class, and `kind` goes to Derived
// in C++ and in the model. The datatype holds the Base member `seen` too, because the value is the whole object.
newtype int32 = x: int | -0x8000_0000 <= x < 0x8000_0000

datatype Derived = Derived(seen: int32)

function kind(d: Derived): int32 { 2 }

method seen_kind() returns (result: int32)
  ensures result == 2
{
  var d := Derived(0);
  d := d.(seen := kind(d));
  result := d.seen;
}
