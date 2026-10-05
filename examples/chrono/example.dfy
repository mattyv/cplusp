// A std::chrono::milliseconds is a datatype of its one field, the count, as an int64, decision 0029. The sum of two is the sum of the
// counts, and Dafny checks that it fits in int64, so the precondition of add is what the C++ contract says. A chrono type has no other
// state, and the unit is in the type, so the model needs no ratio.
newtype int64 = x: int | -0x8000_0000_0000_0000 <= x < 0x8000_0000_0000_0000

datatype Milliseconds = Milliseconds(count: int64)

method add(a: Milliseconds, b: Milliseconds) returns (result: Milliseconds)
  requires -0x8000_0000_0000_0000 <= a.count as int + b.count as int <= 0x7FFF_FFFF_FFFF_FFFF
  ensures result.count as int == a.count as int + b.count as int
{
  result := Milliseconds(a.count + b.count);
}

method deadline(start: Milliseconds, timeout: Milliseconds) returns (result: Milliseconds)
  requires 0 <= start.count <= 1_000_000_000_000 && 0 <= timeout.count <= 1_000_000_000_000
  ensures result.count as int == start.count as int + timeout.count as int
{
  result := add(start, timeout);
}

method one_and_a_half_seconds_after_one() returns (result: Milliseconds)
  ensures result.count == 2500
{
  result := deadline(Milliseconds(1000), Milliseconds(1500));
}
