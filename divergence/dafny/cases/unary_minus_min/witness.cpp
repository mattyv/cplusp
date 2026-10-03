// The edge where the naive model and the C++ part ways: the negative of INT32_MIN is not an int32_t.
#include <cstdint>
#include <cstdio>
#include <limits>

int32_t neg(int32_t x);

int main() {
  std::printf("%d\n", neg(std::numeric_limits<int32_t>::min()));
  return 0;
}
