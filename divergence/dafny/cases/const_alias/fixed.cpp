#include <cstdint>

//@ modifies a
//@ ensures a == 1 && result == old(b)
int32_t set_and_read(int32_t& a, const int32_t& b) {
  a = 1;
  return b;
}

// Two objects. The const reference is a value in, and the result is 0, as the contract says.
int32_t demo() {
  int32_t x = 0;
  int32_t y = 0;
  return set_and_read(x, y);
}
