// The edge where the naive model and the C++ part ways: C++20 defines a left shift of a negative value.
// -1 << 1 is -2, and INT32_MIN << 1 is 0. The sanitizer stays silent in C++20.
#include <cstdint>
#include <cstdio>
#include <limits>

int32_t shl(int32_t x, uint32_t n);

int main() {
  std::printf("%d %d\n", shl(-1, 1), shl(std::numeric_limits<int32_t>::min(), 1));
  return 0;
}
