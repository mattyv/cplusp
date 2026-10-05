// Model B: an interface is an opaque type whose contract is the only thing known about it, decision 0029. Store is a datatype that
// implements both, and it meets each contract on its own type. A reference to Store seen as an interface is a conversion, and a call
// through it is a call on the same value. The conversion is trusted: it is what the vtable of the C++ class does.
newtype int32 = x: int | -0x8000_0000 <= x < 0x8000_0000

type Readable
type Countable

function {:axiom} read(r: Readable): int32
function {:axiom} count(c: Countable): int32

datatype Store = Store(value: int32, items: int32)

function {:axiom} AsReadable(s: Store): Readable
  ensures read(AsReadable(s)) == s.value

function {:axiom} AsCountable(s: Store): Countable
  ensures count(AsCountable(s)) == s.items

method read_of(r: Readable) returns (result: int32)
  ensures result == read(r)
{
  result := read(r);
}

method count_of(c: Countable) returns (result: int32)
  ensures result == count(c)
{
  result := count(c);
}

method both(s: Store) returns (result: int32)
  requires 0 <= s.value <= 1000 && 0 <= s.items <= 1000
  ensures result as int == s.value as int + s.items as int
{
  var a := read_of(AsReadable(s));
  var b := count_of(AsCountable(s));
  result := a + b;
}

// The model proves 7 for 3 and 4, and so does C++.
method Demo() {
  var t := both(Store(3, 4));
  assert t == 7;
}
