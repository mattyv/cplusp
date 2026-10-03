// The edge where the naive model and the C++ part ways: the order of the two arguments is unspecified.
// clang evaluates them left to right and prints 1. g++ evaluates them right to left and prints 0.
#include <cstdint>
#include <cstdio>

bool rises(int32_t& x);

int main() {
  int32_t x = 0;
  std::printf("%d\n", rises(x));
  return 0;
}
