#include <cstdint>
#include <optional>

//@ ensures result.has_value() == (x > 0)
//@ ensures result.has_value() ==> *result == x
std::optional<int32_t> positive(int32_t x) {
  if (x > 0) {
    return x;
  }
  return std::nullopt;
}

// has_value and value read the optional that a call gives, through the temporary that holds it, decision 0133.
//@ ensures result == (x > 0)
bool is_positive(int32_t x) {
  return positive(x).has_value();
}

//@ requires x > 0
//@ ensures result == x
int32_t unwrap(int32_t x) {
  return positive(x).value();
}

//@ requires x > 0
//@ ensures result == x
int32_t star(int32_t x) {
  return *positive(x);
}
