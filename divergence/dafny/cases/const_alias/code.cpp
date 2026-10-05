#include <cstdint>

// The bot read `b` as a value in, so the contract says the result is what `b` held at the call.
//@ modifies a
//@ ensures a == 1 && result == old(b)
int32_t set_and_read(int32_t& a, const int32_t& b) {
  a = 1;
  return b;
}

// One object under both names. The write to `a` is a write to `b`, and the result is 1.
int32_t demo() {
  int32_t x = 0;
  return set_and_read(x, x);
}
