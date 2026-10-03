// The edge where the naive model and the C++ part ways: 1e-16 is below the unit round-off of 1.0.
// The sum rounds to 1.0, and the difference is 0, not 1e-16.
#include <cstdio>

double shifted(double a, double b);

int main() {
  std::printf("%.17g\n", shifted(1e-16, 1.0));
  return 0;
}
