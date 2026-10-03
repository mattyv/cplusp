#include <cstddef>

//@ ensures result == n
size_t count_down(size_t n) {
  size_t steps = 0;
  for (size_t i = n - 1; i < n; --i) {
    ++steps;
  }
  return steps;
}
