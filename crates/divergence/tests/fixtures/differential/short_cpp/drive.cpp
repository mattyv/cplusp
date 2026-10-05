#include <cinttypes>
#include <cstdint>
#include <cstdio>

#include "inputs.h"

int32_t id(int32_t x);

int main() {
  for (std::size_t i = 0; i < 1; ++i) {
    std::printf("%" PRId32 "\n", id(arg0[i]));
  }
  return 0;
}
