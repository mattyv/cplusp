#include <cstdint>
#include <optional>
#include <variant>

// An optional says in its type that a value may be missing, and the contract says when it is. A caller that reads the value must
// have tested has_value, and the prover checks that it did. Half of an even number is exact, and C++ division rounds toward zero.
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

// A variant holds one of its alternatives, and a read of the other one is refused. The contract says which one it holds,
// and the caller that cannot say tests with holds_alternative first.
//@ requires std::holds_alternative<int32_t>(v)
//@ ensures result == std::get<int32_t>(v)
int32_t as_int(const std::variant<int32_t, bool>& v) {
  return std::get<int32_t>(v);
}

//@ ensures result == (std::holds_alternative<int32_t>(v) ? std::get<int32_t>(v) : 0)
int32_t int_or_zero(const std::variant<int32_t, bool>& v) {
  if (!std::holds_alternative<int32_t>(v)) {
    return 0;
  }
  return as_int(v);
}
