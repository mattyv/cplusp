#include <cstdint>

float as_float(uint32_t bits) {
  return *reinterpret_cast<float*>(&bits);  // BANNED
}

void drop_const(const int& x) {
  int& y = const_cast<int&>(x);  // BANNED
  y = 0;
}
