// The edge where the naive model and the C++ part ways: the absolute value of INT32_MIN is not an int32_t.
#include <cstdint>
#include <cstdio>
#include <limits>

int32_t magnitude(int32_t x);

int main() {
  std::printf("%d\n", magnitude(std::numeric_limits<int32_t>::min()));
  return 0;
}
