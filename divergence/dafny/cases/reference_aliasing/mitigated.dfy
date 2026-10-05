// Model B: a non-const reference parameter is a value in and a value out, decision 0029. A value model cannot see two names for
// one object, and a value has no address, so no clause can say it. The gate refuses the call add_both(x, x) at its line, row
// `aliasing`, decision 0033. So every call the model sees passes two objects, and the contract is true for every one of them.
newtype int32 = x: int | -0x8000_0000 <= x < 0x8000_0000

method add_both(a: int32, b: int32) returns (a': int32, b': int32)
  requires -0x1000_0000 <= a < 0x1000_0000
  requires -0x1000_0000 <= b < 0x1000_0000
  ensures a' as int == a as int + b as int
  ensures b' as int == a as int + 2 * (b as int)
{
  a' := a + b;
  b' := b + a';
}

// Two different objects x and y with 3 and 4 end as 7 and 11. The call add_both(x, x) is not a call the gate allows.
method Demo() {
  var x: int32 := 3;
  var y: int32 := 4;
  var a, b := add_both(x, y);
  assert a == 7 && b == 11;
}
