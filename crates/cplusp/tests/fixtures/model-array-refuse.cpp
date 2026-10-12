#include <array>
#include <cstdint>

// An array with no const, and an array in a field, stay out of the subset, decision 0132.
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
