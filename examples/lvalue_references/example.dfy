// A reference is an object with one field, so two references can be the same object. `requires dst != src` is the model of
// `requires &dst != &src`. Delete it and Dafny refuses the contract, which is false when dst and src are one object.
newtype int32 = x: int | -0x8000_0000 <= x < 0x8000_0000

class Ref {
  var v: int32
}

method take(dst: Ref, src: Ref)
  requires dst != src
  modifies dst, src
  ensures dst.v == old(src.v) && src.v == 0
{
  dst.v := src.v;
  src.v := 0;
}
