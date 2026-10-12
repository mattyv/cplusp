#include <array>
#include <cstdint>

// An array with no const, an array in a field, and an array of bool stay out of the subset, decisions 0132 and 0136.
//@ modifies a
int32_t first(std::array<int32_t, 4>& a) {
  return a[0];
}

int32_t copy(std::array<int32_t, 4> a) {
  return a[0];
}

struct Pair {
  std::array<int32_t, 2> v;
};

int32_t left(Pair p) {
  return p.v[0];
}

//@ ensures result == (a[0] || a[1])
bool any(const std::array<bool, 2>& a) {
  return a[0] || a[1];
}
