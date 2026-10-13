#include <cstdint>
#include <span>

// An index line above a loop that is no range-for, an index name that the function also declares, and an index line with two names,
// are refused at their lines, decision 0143.
int32_t plain(int32_t n) {
  int32_t k = 0;
  //@ index i
  while (k < n) {
    ++k;
  }
  return k;
}

int32_t clash(std::span<const int32_t> v) {
  int32_t i = 0;
  //@ index i
  for (int32_t x : v) {
    i = x;
  }
  return i;
}

int32_t two(std::span<const int32_t> v) {
  int32_t t = 0;
  //@ index i, j
  for (int32_t x : v) {
    t = x;
  }
  return t;
}

//@ index i
int32_t above(std::span<const int32_t> v) {
  return 0;
}
