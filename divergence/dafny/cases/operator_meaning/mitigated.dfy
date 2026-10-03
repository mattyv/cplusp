// Model B: `a + b` on a class type is a call to operator+, a method with its own contract.
// `total` follows the contract of the call, never the built-in sum.
newtype int32 = x: int | -0x8000_0000 <= x < 0x8000_0000

datatype Money = Money(cents: int32)

method plus(a: Money, b: Money) returns (result: Money)
  requires 0 <= a.cents <= 1000 && 0 <= b.cents <= 1000
  ensures result.cents as int == (if a.cents as int + b.cents as int > 1000 then 1000 else a.cents as int + b.cents as int)
{
  if a.cents + b.cents > 1000 {
    result := Money(1000);
  } else {
    result := Money(a.cents + b.cents);
  }
}

method total(a: Money, b: Money) returns (result: Money)
  requires 0 <= a.cents <= 1000 && 0 <= b.cents <= 1000
  ensures result.cents as int == (if a.cents as int + b.cents as int > 1000 then 1000 else a.cents as int + b.cents as int)
{
  result := plus(a, b);
}

// The model proves 1000 for 600 and 600, and so does C++.
method Demo() {
  var r := total(Money(600), Money(600));
  assert r.cents == 1000;
}
