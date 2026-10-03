// Model B: the constructor is modelled in declaration order, a first and then b, whatever order the C++ writes.
// The contract is the one in code.cpp. The fixed C++ also writes the mem-initializers in this order.
newtype int32 = x: int | -0x8000_0000 <= x < 0x8000_0000

datatype Pair = Pair(a: int32, b: int32)

method next(counter0: int32) returns (counter: int32, result: int32)
  requires counter0 < 0x7FFF_FFFF
  ensures counter == counter0 + 1 && result == counter
{
  counter := counter0 + 1;
  result := counter;
}

method make_pair(counter0: int32) returns (counter: int32, p: Pair)
  requires counter0 <= 0x7FFF_FFF0
  ensures p.a as int == counter0 as int + 1 && p.b as int == counter0 as int + 2
{
  var c1, a := next(counter0);
  var c2, b := next(c1);
  counter := c2;
  p := Pair(a, b);
}

method make() returns (p: Pair)
  ensures p.a == 1 && p.b == 2
{
  var c, q := make_pair(0);
  p := q;
}
