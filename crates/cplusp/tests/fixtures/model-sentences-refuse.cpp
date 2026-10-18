#include <cmath>
#include <cstdint>

// Each refusal names its own cause, decision 0155.
//@ requires std::isfinite(x) && std::isnan(x)
double unread(double x) {
  return x;
}

//@ requires std::isfinite(x)
int32_t rem_of_cast(double x) {
  return static_cast<int32_t>(x) % 2;
}

//@ ensures result >= 0.00000000000000000001
double tiny() {
  return 1.0;
}

void unnamed(int32_t&) {
}

double unnamed_d(double) {
  return 0.0;
}
