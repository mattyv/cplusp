// The edge where the naive model and the C++ part ways: 0.1, 0.2 and 0.3 are not doubles.
// Each is the nearest double, and the sum of the first two rounds to a different double than the third.
#include <cstdio>

double sum(double a, double b);

int main() {
  std::printf("%d\n", sum(0.1, 0.2) == 0.3);
  return 0;
}
