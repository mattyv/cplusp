#include <cstdint>

//@ ensures result == x
int8_t narrow(int32_t x) {
  return static_cast<int8_t>(x);
}
