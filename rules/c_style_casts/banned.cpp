#include <cstdint>

int32_t narrow(int64_t big) {
  return (int32_t)big;  // BANNED
}

// A functional cast with parentheses is a C-style cast in other clothes.
int32_t narrow_functional(int64_t big) {
  return int32_t(big);  // BANNED
}
