#include <cstdint>

float as_float(uint32_t bits) {
  return *reinterpret_cast<float*>(&bits);  // BANNED
}

void drop_const(const int32_t& x) {
  int32_t& y = const_cast<int32_t&>(x);  // BANNED
  y = 0;
}
