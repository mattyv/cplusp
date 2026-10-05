#include <cstdint>
#pragma clang fp contract(fast)
double axpy(double a, double x, double y) {
  const double t = a * x;
  return t + y;
}
