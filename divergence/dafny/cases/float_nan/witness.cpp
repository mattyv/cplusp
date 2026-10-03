// The edge where the naive model and the C++ part ways: a NaN is not equal to itself.
// The second call has finite arguments and keeps the precondition of fixed.cpp.
// The first call breaks it. It is here to show the edge, and a caller of fixed.cpp must not make it.
#include <cstdio>
#include <limits>

bool same(double a, double b);

int main() {
  double nan = std::numeric_limits<double>::quiet_NaN();
  std::printf("%d %d\n", same(nan, nan), same(1.0, 1.0));
  return 0;
}
