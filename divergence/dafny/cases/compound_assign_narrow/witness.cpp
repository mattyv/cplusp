// The edge where the naive model and the C++ part ways: 200 + 100 is 300 in int, and 44 after the conversion back.
#include <cstdint>
#include <cstdio>

uint8_t bump(uint8_t a);

int main() {
  std::printf("%d\n", bump(200));
  return 0;
}
