#include <cstdint>

// A function with no body and no marker has no method, so a call of it is refused, decision 0102.
//@ ensures result <= 255
uint32_t read_status();

uint32_t reads() {
  uint32_t s = read_status();
  return s;
}
