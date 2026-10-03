// The edge where the naive model and the C++ part ways: INT32_MAX + 1 is not an int32_t.
#include <cstdint>
#include <cstdio>
#include <limits>

int32_t next(int32_t x);

int main() {
  std::printf("%d\n", next(std::numeric_limits<int32_t>::max()));
  return 0;
}
