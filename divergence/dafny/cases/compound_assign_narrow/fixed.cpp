#include <cstdint>

//@ ensures result == (a + 100) mod 256
uint8_t bump(uint8_t a) {
  a = static_cast<uint8_t>(a + 100);
  return a;
}
