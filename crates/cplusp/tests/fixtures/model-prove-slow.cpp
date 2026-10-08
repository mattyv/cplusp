#include <cstdint>

// A contract that the prover cannot settle in one second, decision 0068. The result is unknown, not false.
//@ ensures a * a * b * c * c * b != 12345678901
int32_t slow(int32_t a, int32_t b, int32_t c) {
  return a;
}
