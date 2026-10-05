// A struct passed by reference is an object. The trusted copy is a method with no body, an axiom with the contract of
// trusted.cpp. `requires dst != src` is the model of `requires &dst != &src`. The caller has the same requirement for its two objects.
newtype int32 = x: int | -0x8000_0000 <= x < 0x8000_0000

class Pair {
  var a: int32
  var b: int32
}

method {:axiom} copy_pair(dst: Pair, src: Pair)
  requires dst != src
  modifies dst
  ensures dst.a == src.a && dst.b == src.b

method swapped_copy(out: Pair, p: Pair)
  requires out != p
  modifies out
  ensures out.a == p.b && out.b == p.a
{
  copy_pair(out, p);
  var t := out.a;
  out.a := out.b;
  out.b := t;
}
