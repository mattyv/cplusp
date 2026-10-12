#include <cstdint>
#include <optional>

struct Pair {
  int32_t lo;
  int32_t hi;
};

//@ ensures result.has_value() == (a <= b)
std::optional<Pair> ordered(int32_t a, int32_t b) {
  if (a > b) {
    return std::nullopt;
  }
  return Pair{a, b};
}

// A read through `->` of an optional that may be empty does not prove, in code and in a contract, decision 0137.
int32_t upper(int32_t a, int32_t b) {
  std::optional<Pair> p = ordered(a, b);
  return p->hi;
}

//@ ensures result->lo == a
std::optional<Pair> first(int32_t a, int32_t b) {
  return ordered(a, b);
}
