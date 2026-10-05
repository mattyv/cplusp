#include <cstdint>

double as_double(uint64_t bits) {
  return *reinterpret_cast<double*>(&bits);  // BANNED
}

void drop_const(const int32_t& x) {
  int32_t& y = const_cast<int32_t&>(x);  // BANNED also: lvalue_references
  y = 0;
}
