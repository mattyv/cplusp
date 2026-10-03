// The edge for the model: -7 >> 1 rounds toward negative infinity. C++20 defines it, and Dafny `/` rounds the same way.
#include <cstdint>
#include <cstdio>

int32_t shr(int32_t x, uint32_t n);

int main() {
  std::printf("%d\n", shr(-7, 1));
  return 0;
}
