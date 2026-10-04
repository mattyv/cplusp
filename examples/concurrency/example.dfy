// The getter is a method with no body, an axiom that states the contract of trusted.cpp. It is a method and
// not a function, so two calls may return two values. The caller proves its result from the range alone.
newtype int32 = x: int | -0x8000_0000 <= x < 0x8000_0000

method {:axiom} level() returns (result: int32)
  ensures 0 <= result <= 100

method level_percent() returns (result: int32)
  ensures 0 <= result <= 100
{
  var l := level();
  result := if l > 100 then 100 else l;
}
