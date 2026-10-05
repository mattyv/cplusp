// A struct is a datatype, decision 0029. The trusted copy is a method with no body, an axiom with the contract of trusted.cpp,
// and it takes the destination in and gives it back. A value has no address, so the model never sees two names for one object.
// The gate refuses a call that passes one object under two names, row aliasing, decision 0033.
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
