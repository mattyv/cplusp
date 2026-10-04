#include <cstdint>

// A value another thread changes enters verified code through a trusted getter. Its contract says what every
// writer keeps, a range, and nothing about two reads being equal. The body is in trusted.cpp.
//@ ensures 0 <= result <= 100
int32_t level();

// The caller relies on the range alone. It reads once, and it never assumes a second read agrees.
//@ ensures 0 <= result <= 100
int32_t level_percent() {
  int32_t l = level();
  return l > 100 ? 100 : l;
}
