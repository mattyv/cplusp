#include <cstdint>
#include <optional>
#include <span>

// A chain of three comparisons means each of them, decision 0131. The ensures line needs the last one.
//@ requires 0 <= x < y < 100
//@ ensures 0 < result < 100
int32_t upper(int32_t x, int32_t y) {
  return y;
}

// The sorted form of binary_search. The ensures line needs the pair of the first and the last index.
//@ requires 0 < v.size()
//@ requires forall i, j :: 0 <= i < j < v.size() ==> v[i] <= v[j]
//@ ensures result <= v[v.size() - 1]
int32_t first(std::span<const int32_t> v) {
  return v[0];
}

// `*o` reads the value of an optional, decision 0131.
//@ ensures result.has_value() ==> *result == x
std::optional<int32_t> keep(int32_t x) {
  if (x < 0) {
    return std::nullopt;
  }
  return x;
}
