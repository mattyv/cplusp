#include <cinttypes>
#include <cstdint>
#include <cstdio>

#include "inputs.h"

int32_t id(int32_t x);

int main() {
  for (std::size_t i = 0; i < runs; ++i) {
    if (i == 1) {
      throw 1;
    }
    std::printf("%" PRId32 "\n", id(arg0[i]));
  }
  return 0;
}
