// The edge where the naive model and the C++ part ways: -1 becomes the largest size_t.
#include <cstddef>
#include <cstdint>
#include <cstdio>

std::size_t index_of(int32_t i);

int main() {
  // This call breaks the precondition of fixed.cpp. The prover refuses such a caller. The output shows only that the cast is deterministic.
  std::printf("%zu\n", index_of(-1));
  return 0;
}
