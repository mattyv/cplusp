// The edge where the naive model and the C++ part ways: the float sum of 1 and 1e-8 is 1, so the error is 1e-8.
// The double bound allows about 1e-16. The program prints 1 when the error is above that bound.
#include <cfloat>
#include <cmath>
#include <cstdio>

double sum(double a, double b);

int main() {
  double got = sum(1.0, 1e-8);
  double exact = 1.0 + 1e-8;
  double error = std::fabs(got - exact);
  double slack = DBL_EPSILON / 2 * exact;
  double bound = slack + DBL_TRUE_MIN / 2;
  std::printf("%d\n", error > bound);
  return 0;
}
