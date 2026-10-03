// The edge where the naive model and the C++ part ways: for int8_t, 2 * 100 is 200 in int, and the return narrows it.
// C++20 keeps the low 8 bits, so the result is -56.
#include <cstdint>
#include <cstdio>

int8_t twice8(int8_t x);

int main() {
  // This call breaks the precondition of fixed.cpp. The prover refuses such a caller. The output shows only that the cast is deterministic.
  std::printf("%d\n", twice8(100));
  return 0;
}
