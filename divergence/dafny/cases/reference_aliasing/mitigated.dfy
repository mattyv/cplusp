// Model B: a reference is an object with one field, so two references can be the same object.
// Delete `requires a != b` and Dafny refuses the contract. It is false when a and b are the same object.
newtype int32 = x: int | -0x8000_0000 <= x < 0x8000_0000

class Ref {
  var v: int32
}

method add_both(a: Ref, b: Ref)
  requires a != b
  requires -0x1000_0000 <= a.v < 0x1000_0000
  requires -0x1000_0000 <= b.v < 0x1000_0000
  modifies a, b
  ensures a.v as int == old(a.v) as int + old(b.v) as int
  ensures b.v as int == old(a.v) as int + 2 * (old(b.v) as int)
{
  a.v := a.v + b.v;
  b.v := b.v + a.v;
}
