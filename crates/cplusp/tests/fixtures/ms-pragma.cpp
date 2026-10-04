#include <cstdint>
__pragma(clang diagnostic ignored "-Wreturn-stack-address")
const int32_t& f() {
  int32_t x = 1;
  return x;
}
