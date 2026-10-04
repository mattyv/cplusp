// The edge where the naive model and the C++ part ways: 0.1 is not a double, so a * 0.1 rounds twice.
// tenth(3.0) misses the real 0.3 by 4.4e-17, and the one-rounding bound allows 3.3e-17. The program prints 1 when it is missed.
// The real 0.3 is held in long double, which has more digits than the double bound can see.
#include <cfloat>
#include <cmath>
#include <cstdio>

double tenth(double a);

int main() {
  double got = tenth(3.0);
  long double exact = 3.0L / 10.0L;
  long double error = std::fabs(got - exact);
  long double slack = DBL_EPSILON / 2 * exact;
  long double bound = slack + DBL_TRUE_MIN / 2;
  std::printf("%d\n", error > bound);
  return 0;
}
