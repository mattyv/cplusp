// The edge where the naive model and the C++ part ways: set_and_read(x, x) writes the object the const reference reads.
// code.cpp prints 1. fixed.cpp passes two objects and prints 0, as the contract says.
#include <cstdint>
#include <cstdio>

int32_t demo();

int main() {
  std::printf("%d\n", demo());
  return 0;
}
