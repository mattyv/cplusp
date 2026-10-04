// A pure interface is a trait. A class that implements several interfaces extends several traits, and dispatch through any of
// them is the same call. The data of the concrete base, the id, is a field of the class, since a Dafny class has one parent.
newtype uint32 = x: int | 0 <= x < 0x1_0000_0000
newtype uint64 = x: int | 0 <= x < 0x1_0000_0000_0000_0000

trait Sized {
  function size(): uint32
    reads this
}

trait Weighed {
  function weight(): uint32
    reads this
}

class Crate extends Sized, Weighed {
  var id: uint32
  var size_: uint32
  var weight_: uint32

  constructor (id: uint32, size: uint32, weight: uint32)
    ensures this.id == id && size_ == size && weight_ == weight
  {
    this.id := id;
    size_ := size;
    weight_ := weight;
  }

  function size(): uint32
    reads this
    ensures size() == size_
  {
    size_
  }

  function weight(): uint32
    reads this
    ensures weight() == weight_
  {
    weight_
  }
}

method both(c: Crate) returns (result: uint64)
  ensures result as int == c.size() as int + c.weight() as int
{
  var s: Sized := c;
  var w: Weighed := c;
  var a := s.size();
  var b := w.weight();
  result := (a as uint64) + (b as uint64);
}
