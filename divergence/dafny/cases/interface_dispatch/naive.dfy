// Model A: each interface is a trait, and Store is a class that extends both.
// A call through either trait goes to the function of Store, as in C++. The literal model is exact.
newtype int32 = x: int | -0x8000_0000 <= x < 0x8000_0000

trait Readable {
  function read(): int32
    reads this
}

trait Countable {
  function count(): int32
    reads this
}

class Store extends Readable, Countable {
  var value: int32
  var items: int32
  function read(): int32
    reads this
  { value }
  function count(): int32
    reads this
  { items }
}

method both(s: Store) returns (result: int32)
  requires 0 <= s.value <= 1000 && 0 <= s.items <= 1000
  ensures result as int == s.value as int + s.items as int
{
  var r: Readable := s;
  var c: Countable := s;
  var a := r.read();
  var b := c.count();
  result := a + b;
}

// The model proves 7 for 3 and 4, and so does C++.
method Demo() {
  var s := new Store;
  s.value := 3;
  s.items := 4;
  var t := both(s);
  assert t == 7;
}
