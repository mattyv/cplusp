// The edge where the naive model and the C++ part ways: 7 is not 1, and it still converts to true.
#include <cstdint>
#include <cstdio>

bool nonzero(int32_t x);

int main() {
  std::printf("%d\n", nonzero(7));
  return 0;
}
