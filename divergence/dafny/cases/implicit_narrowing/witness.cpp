// The edge where the naive model and the C++ part ways: 2^32 + 5 does not fit in int32_t. C++20 keeps the low 32 bits.
#include <cstdint>
#include <cstdio>

int32_t low(int64_t x);

int main() {
  // This call breaks the precondition of fixed.cpp. The prover refuses such a caller. The output shows only that the cast is deterministic.
  std::printf("%d\n", low((1LL << 32) | 5));
  return 0;
}
