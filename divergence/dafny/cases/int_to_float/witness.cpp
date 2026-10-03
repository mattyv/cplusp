// The edge where the naive model and the C++ part ways: 2^53 + 1 is not a double.
// It is halfway between two doubles, and the conversion picks the even one, 2^53.
#include <cstdint>
#include <cstdio>

double widen(int64_t n);

int main() {
  std::printf("%.17g\n", widen(9007199254740993));
  return 0;
}
