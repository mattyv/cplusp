// A reference is an object with one field, so two references can be the same object. `requires a != b` is the model
// of `requires &a != &b`. The proof of the swap holds only when the two objects differ.
newtype int32 = x: int | -0x8000_0000 <= x < 0x8000_0000

class Ref {
  var v: int32
}

method swap_values(a: Ref, b: Ref)
  requires a != b
  modifies a, b
  ensures a.v == old(b.v) && b.v == old(a.v)
{
  var t := a.v;
  a.v := b.v;
  b.v := t;
}
