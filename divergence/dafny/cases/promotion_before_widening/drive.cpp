// The differential driver: the product as a decimal int64.
#include <cinttypes>
#include <cstdint>
#include <cstdio>

#include "inputs.h"

int64_t product(int32_t a, int32_t b);

int main() {
  for (std::size_t i = 0; i < runs; ++i) {
    std::printf("%" PRId64 "\n", product(arg0[i], arg1[i]));
  }
  return 0;
}
