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

// A read of the value of a call that may give none does not prove, decision 0133.
int32_t unwrap(int32_t x) {
  return positive(x).value();
}
