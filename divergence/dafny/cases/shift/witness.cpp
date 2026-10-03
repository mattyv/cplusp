// The edge where the naive model and the C++ part ways: a shift by the full width is undefined.
#include <cstdint>
#include <cstdio>

uint32_t shl(uint32_t x, uint32_t n);

int main() {
  std::printf("%u\n", shl(1, 32));
  return 0;
}
