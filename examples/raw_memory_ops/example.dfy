// A struct passed by reference is an object. The trusted copy is a method with no body, an axiom with the contract of
// trusted.cpp. `requires dst != src` is the model of `requires &dst != &src`. The new local is a fresh object, so it differs.
newtype int32 = x: int | -0x8000_0000 <= x < 0x8000_0000

class Pair {
  var a: int32
  var b: int32
  constructor () ensures a == 0 && b == 0 { a := 0; b := 0; }
}

method {:axiom} copy_pair(dst: Pair, src: Pair)
  requires dst != src
  modifies dst
  ensures dst.a == src.a && dst.b == src.b

method duplicate(p: Pair) returns (result: Pair)
  ensures result.a == p.a && result.b == p.b
{
  var q := new Pair();
  copy_pair(q, p);
  result := q;
}
