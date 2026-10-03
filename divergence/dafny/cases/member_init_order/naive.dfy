// Model A: the constructor assigns in the order the mem-initializers are written, b first and then a.
// The contract is the one that order gives. It verifies. C++ initializes a first.
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
  ensures p.b as int == counter0 as int + 1 && p.a as int == counter0 as int + 2
{
  var c1, b := next(counter0);
  var c2, a := next(c1);
  counter := c2;
  p := Pair(a, b);
}

// The model proves b == 1 and a == 2. In C++ the result is a == 1 and b == 2.
method make() returns (p: Pair)
  ensures p.b == 1 && p.a == 2
{
  var c, q := make_pair(0);
  p := q;
}
