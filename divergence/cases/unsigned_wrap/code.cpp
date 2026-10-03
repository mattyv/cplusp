#include <cstdint>

//@ ensures result == (a - b) mod 4294967296
uint32_t sub(uint32_t a, uint32_t b) {
  return a - b;
}
