// The edge where the naive model and the C++ part ways: n - 1 for n == 0 wraps to the largest size_t.
// The loop relies on that wrap, so it runs zero times. Nothing here is undefined.
#include <cstddef>
#include <cstdio>

size_t count_down(size_t n);

int main() {
  size_t n = 0;
  std::printf("%zu %zu\n", n - 1, count_down(n));
  return 0;
}
