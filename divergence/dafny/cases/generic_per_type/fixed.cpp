#include <cstdint>

template <class T>
T twice(T x) {
  return static_cast<T>(2 * x);
}

//@ requires -64 <= x < 64
//@ ensures result == 2 * x
int8_t twice8(int8_t x) {
  return twice(x);
}
