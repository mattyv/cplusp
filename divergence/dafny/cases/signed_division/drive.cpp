// The differential driver: quotient and remainder on one line, or skip where the contract does not reach.
#include <cinttypes>
#include <cstdint>
#include <cstdio>

#include "inputs.h"

int32_t quot(int32_t a, int32_t b);
int32_t rem(int32_t a, int32_t b);

int main() {
  for (std::size_t i = 0; i < runs; ++i) {
    const int32_t a = arg0[i];
    const int32_t b = arg1[i];
    if (b == 0 || (a == INT32_MIN && b == -1)) {
      std::printf("skip\n");
    } else {
      std::printf("%" PRId32 " %" PRId32 "\n", quot(a, b), rem(a, b));
    }
  }
  return 0;
}
