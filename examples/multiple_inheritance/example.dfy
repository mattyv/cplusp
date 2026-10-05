// A pure interface is an opaque type with its contract as the only functions known about it, decision 0029. The concrete base Item
// is a datatype, and Crate holds it as a field, because the value is the whole object. Crate is its own datatype with the functions
// that meet each interface. A reference to a Crate seen as an interface is a conversion, and a call through it is a call on the same
// value. The conversions are trusted: they are what the vtables of the C++ class do.
newtype uint32 = x: int | 0 <= x < 0x1_0000_0000
newtype uint64 = x: int | 0 <= x < 0x1_0000_0000_0000_0000

datatype Item = Item(id_: uint32)

function id(i: Item): uint32 { i.id_ }

method MakeItem(id: uint32) returns (i: Item)
  ensures i.id_ == id
{
  i := Item(id);
}

type Sized
type Weighed

function {:axiom} size(s: Sized): uint32
function {:axiom} weight(w: Weighed): uint32

datatype Crate = Crate(item: Item, size_: uint32, weight_: uint32)

function crate_size(c: Crate): uint32 { c.size_ }

function crate_weight(c: Crate): uint32 { c.weight_ }

method MakeCrate(id: uint32, size: uint32, weight: uint32) returns (c: Crate)
  ensures c.item.id_ == id && c.size_ == size && c.weight_ == weight
{
  var i := MakeItem(id);
  c := Crate(i, size, weight);
}

function {:axiom} AsSized(c: Crate): Sized
  ensures size(AsSized(c)) == crate_size(c)

function {:axiom} AsWeighed(c: Crate): Weighed
  ensures weight(AsWeighed(c)) == crate_weight(c)

method size_of(s: Sized) returns (result: uint64)
  ensures result as int == size(s) as int
{
  result := size(s) as uint64;
}

method weight_of(w: Weighed) returns (result: uint64)
  ensures result as int == weight(w) as int
{
  result := weight(w) as uint64;
}

method both(c: Crate) returns (result: uint64)
  ensures result as int == crate_size(c) as int + crate_weight(c) as int
{
  var a := size_of(AsSized(c));
  var b := weight_of(AsWeighed(c));
  result := a + b;
}
