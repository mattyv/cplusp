// A struct is a datatype, decision 0029. The trusted copy is a method with no body, an axiom with the contract of trusted.cpp,
// and it takes the destination in and gives it back. The C++ clause `requires &dst != &src` has no counterpart on values. The
// caller has the same requirement for its two objects.
newtype int32 = x: int | -0x8000_0000 <= x < 0x8000_0000

datatype Pair = Pair(a: int32, b: int32)

method {:axiom} copy_pair(dst: Pair, src: Pair) returns (dst': Pair)
  ensures dst'.a == src.a && dst'.b == src.b

method swapped_copy(out: Pair, p: Pair) returns (out': Pair)
  ensures out'.a == p.b && out'.b == p.a
{
  var o := copy_pair(out, p);
  var t := o.a;
  o := o.(a := o.b);
  o := o.(b := t);
  out' := o;
}
