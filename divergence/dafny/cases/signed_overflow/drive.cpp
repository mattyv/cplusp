// The differential driver: the C++ on the generated inputs, one line per input, in the format drive.dfy prints.
#include <cinttypes>
#include <cstdint>
#include <cstdio>

#include "inputs.h"

int32_t add(int32_t a, int32_t b);

int main() {
  for (std::size_t i = 0; i < runs; ++i) {
    std::printf("%" PRId32 "\n", add(arg0[i], arg1[i]));
  }
  return 0;
}
