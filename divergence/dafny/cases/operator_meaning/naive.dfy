// Model A: `a + b` is the built-in sum of the two cents fields, and the contract is written for that sum.
// It verifies. The C++ calls operator+, which saturates at 1000.
newtype int32 = x: int | -0x8000_0000 <= x < 0x8000_0000

datatype Money = Money(cents: int32)

method total(a: Money, b: Money) returns (result: Money)
  requires 0 <= a.cents <= 1000 && 0 <= b.cents <= 1000
  ensures result.cents as int == a.cents as int + b.cents as int
{
  result := Money(a.cents + b.cents);
}

// The model proves 1200 for 600 and 600. In C++ the result is 1000.
method Demo() {
  var r := total(Money(600), Money(600));
  assert r.cents == 1200;
}
