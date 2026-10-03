#include <cstdint>

//@ ensures result == x + 1
int32_t next(int32_t x) {
  ++x;
  return x;
}
