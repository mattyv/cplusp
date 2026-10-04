// The trusted function is a method with no body, an axiom that states the contract of trusted.cpp. The model has real numbers,
// and no NaN, so std::isfinite has no clause here. The caller compares and returns, and proves the clamp from the range alone.
method {:axiom} sensor_reading() returns (result: real)
  ensures -50.0 <= result <= 150.0

method bounded_reading() returns (result: real)
  ensures 0.0 <= result <= 100.0
{
  var r := sensor_reading();
  if r < 0.0 {
    return 0.0;
  }
  if r > 100.0 {
    return 100.0;
  }
  return r;
}
