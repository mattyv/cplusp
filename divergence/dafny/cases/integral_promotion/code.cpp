#include <cstdint>

//@ ensures result == (a + b) mod 256
uint8_t add8(uint8_t a, uint8_t b) {
  return a + b;
}
