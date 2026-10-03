// The edge where the naive model and the C++ part ways: add_both(x, x) is one object, not two.
// Prints the aliased result, then the two results of the separate call that the naive model describes.
#include <cstdint>
#include <cstdio>

void add_both(int32_t& a, int32_t& b);

int main() {
  int32_t x = 3;
  add_both(x, x);
  int32_t a = 3;
  int32_t b = 3;
  add_both(a, b);
  std::printf("%d %d %d\n", x, a, b);
  return 0;
}
