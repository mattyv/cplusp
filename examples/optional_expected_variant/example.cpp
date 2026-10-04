#include <cstdint>
#include <optional>

// An optional says in its type that a value may be missing, and the contract says when it is. A caller that reads the
// value must have tested has_value, and the prover checks that it did. Half of an even number is exact.
//@ ensures result.has_value() == (x % 2 == 0)
//@ ensures result.has_value() ==> *result == x / 2
std::optional<int32_t> half_of_even(int32_t x) {
  if (x % 2 != 0) {
    return std::nullopt;
  }
  return x / 2;
}

//@ ensures result == (x % 2 == 0 ? x / 2 : fallback)
int32_t half_or(int32_t x, int32_t fallback) {
  std::optional<int32_t> h = half_of_even(x);
  if (!h.has_value()) {
    return fallback;
  }
  return *h;
}
