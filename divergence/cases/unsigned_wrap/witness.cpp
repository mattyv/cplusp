// The edge where the naive model and the C++ part ways: a < b wraps, and the C++ is defined.
#include <cstdint>
#include <cstdio>

uint32_t sub(uint32_t a, uint32_t b);

int main() {
  std::printf("%u\n", sub(1, 2));
  return 0;
}
