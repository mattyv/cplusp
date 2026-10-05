#include <cstdint>
#pragma STDC FP_CONTRACT ON
double axpy(double a, double x, double y) {
  const double t = a * x;
  return t + y;
}
