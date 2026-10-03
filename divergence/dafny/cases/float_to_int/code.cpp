#include <cstdint>

//@ ensures result == trunc(x)
int32_t whole(double x) {
  return static_cast<int32_t>(x);
}
