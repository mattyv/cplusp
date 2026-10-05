// Model B: the same values, decision 0029. The gate refuses set_and_read(x, x) at its line, row `aliasing`, decision 0033,
// so the only calls the model sees pass two objects. For those the const reference is a value in, and the contract is true.
newtype int32 = x: int | -0x8000_0000 <= x < 0x8000_0000

method set_and_read(a: int32, b: int32) returns (a': int32, result: int32)
  ensures a' == 1 && result == b
{
  a' := 1;
  result := b;
}

// Two objects x and y, both 0. x ends as 1 and the result is 0, as fixed.cpp prints.
method Demo() {
  var x: int32 := 0;
  var y: int32 := 0;
  var x', r := set_and_read(x, y);
  assert x' == 1 && r == 0;
}
