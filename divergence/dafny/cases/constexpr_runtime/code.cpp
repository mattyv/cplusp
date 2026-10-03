#include <cstdint>

//@ ensures result == x * x
constexpr int32_t square(int32_t x) {
  return x * x;
}
