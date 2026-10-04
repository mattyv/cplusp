#include <cstdint>
#pragma \
clang diagnostic ignored "-Wreturn-stack-address"
#pragma clang/**/diagnostic ignored "-Wswitch"
%:pragma clang diagnostic ignored "-Wunused"
const int32_t& f() {
  int32_t x = 1;
  return x;
}
