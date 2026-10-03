// The edge where the naive model and the C++ part ways: the width of int is not in the source.
// On this target int has 32 bits and the model holds. With a 16-bit int, `twice(20000)` overflows.
#include <climits>
#include <cstdio>

int twice(int x);

int main() {
  std::printf("%zu %d\n", sizeof(int) * CHAR_BIT, twice(20000));
  return 0;
}
