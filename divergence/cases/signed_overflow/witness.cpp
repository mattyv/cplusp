// The edge where the naive model and the C++ part ways.
#include <cstdint>
#include <cstdio>
#include <limits>

int32_t add(int32_t a, int32_t b);

int main() {
  std::printf("%d\n", add(std::numeric_limits<int32_t>::max(), 1));
  return 0;
}
