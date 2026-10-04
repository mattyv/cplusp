// The edge where the naive model and the C++ part ways: 1e-400 is below the smallest subnormal.
// The product rounds to 0, not 1e-400.
#include <cstdio>

double scaled(double a, double b);

int main() {
  std::printf("%.17g\n", scaled(1e-200, 1e-200));
  return 0;
}
