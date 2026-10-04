#include <cstdint>
#pragma clang diagnostic ignored "-Wreturn-stack-address"
#pragma GCC diagnostic push
_Pragma("clang diagnostic ignored \"-Wswitch\"")
const int32_t& f() {
  int32_t x = 1;
  return x;
}
