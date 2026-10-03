// The edge where the naive model and the C++ part ways: 255 + 1 is 256 in int, and 0 after the conversion.
#include <cstdint>
#include <cstdio>

uint8_t add8(uint8_t a, uint8_t b);

int main() {
  std::printf("%d\n", add8(255, 1));
  return 0;
}
