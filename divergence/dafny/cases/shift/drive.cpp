// The differential driver: the shifted value as a decimal, as drive.dfy prints it.
#include <cinttypes>
#include <cstdint>
#include <cstdio>

#include "inputs.h"

uint32_t shl(uint32_t x, uint32_t n);

int main() {
  for (std::size_t i = 0; i < runs; ++i) {
    std::printf("%" PRIu32 "\n", shl(arg0[i], arg1[i]));
  }
  return 0;
}
