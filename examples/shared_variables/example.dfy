// The getter is a method with no body, an axiom that states the range. It is a method and not a function, so two calls may
// return two values. The caller proves its result from the range of one read.
newtype int32 = x: int | -0x8000_0000 <= x < 0x8000_0000

method {:axiom} read_temperature() returns (result: int32)
  ensures 0 <= result < 1000

method headroom_of(t: int32) returns (result: int32)
  requires 0 <= t < 1000
  ensures result == 1000 - t
{
  result := 1000 - t;
}

method headroom() returns (result: int32)
  ensures 0 < result <= 1000
{
  var t := read_temperature();
  result := headroom_of(t);
}
