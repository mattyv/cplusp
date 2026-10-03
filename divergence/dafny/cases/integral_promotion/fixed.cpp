#include <cstdint>

//@ ensures result == (a + b) mod 256
uint8_t add8(uint8_t a, uint8_t b) {
  return static_cast<uint8_t>(a + b);
}
