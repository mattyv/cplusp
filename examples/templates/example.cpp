#include <cstdint>

// A template has type parameters only and no specialisation. It is verified once for each type it is used at, so each
// instantiation has its own model. The contract is the same, and the types carry the difference.
template <typename T>
T larger(T a, T b) {
  return a < b ? b : a;
}

//@ ensures result >= a && result >= b && (result == a || result == b)
int32_t larger32(int32_t a, int32_t b) {
  return larger(a, b);
}

//@ ensures result >= a && result >= b && (result == a || result == b)
uint8_t larger8(uint8_t a, uint8_t b) {
  return larger(a, b);
}
