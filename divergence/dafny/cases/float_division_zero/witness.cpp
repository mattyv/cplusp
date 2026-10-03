// The edge where the naive model and the C++ part ways: the divisor is zero.
// IEEE 754 gives infinity, and C++ calls it undefined. The sanitizer reports the division.
#include <cstdio>

double ratio(double a, double b);

int main() {
  std::printf("%.17g\n", ratio(1.0, 0.0));
  return 0;
}
