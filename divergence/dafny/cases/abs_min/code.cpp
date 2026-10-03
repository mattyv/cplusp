#include <cstdint>
#include <cstdlib>

//@ ensures result == (x < 0 ? -x : x)
int32_t magnitude(int32_t x) {
  return std::abs(x);
}
