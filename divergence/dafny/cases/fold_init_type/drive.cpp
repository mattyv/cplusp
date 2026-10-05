// The differential driver: the sum of each generated vector as a decimal int64.
#include <cinttypes>
#include <cstdint>
#include <cstdio>
#include <vector>

#include "inputs.h"

int64_t total(const std::vector<int64_t>& v);

int main() {
  for (std::size_t i = 0; i < runs; ++i) {
    std::printf("%" PRId64 "\n", total(arg0[i]));
  }
  return 0;
}
