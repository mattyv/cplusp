#include <cstdint>
#define once clang diagnostic ignored "-Wreturn-stack-address"
__pragma(once)
const int32_t& f() {
  int32_t x = 1;
  return x;
}
