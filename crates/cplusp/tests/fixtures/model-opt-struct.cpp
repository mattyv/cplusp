#include <cstdint>
#include <optional>

// An optional of a plain struct, and `->` that reads a field of its value, decision 0137.
struct Pair {
  int32_t lo;
  int32_t hi;
};

//@ ensures result.has_value() == (a <= b)
//@ ensures result.has_value() ==> result->lo == a && result->hi == b
std::optional<Pair> ordered(int32_t a, int32_t b) {
  if (a > b) {
    return std::nullopt;
  }
  return Pair{a, b};
}

//@ requires a <= b
//@ ensures result == b
int32_t upper(int32_t a, int32_t b) {
  std::optional<Pair> p = ordered(a, b);
  return p->hi;
}

//@ ensures result == (a <= b ? a : b)
int32_t lower(int32_t a, int32_t b) {
  std::optional<Pair> p = ordered(a, b);
  if (!p.has_value()) {
    return b;
  }
  return p.value().lo;
}
