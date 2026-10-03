#include <cstdint>

template <class T>
T twice(T x) {
  return 2 * x;
}

//@ ensures result == 2 * x
int8_t twice8(int8_t x) {
  return twice(x);
}
