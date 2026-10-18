#include <cfloat>
#include <cmath>
#include <cstdint>

// A named double constant in code and in a contract, an exact double with no short decimal, and a whole number next to a real,
// decision 0158. A product with the true value of T is 1, so a printer that drops the quotient fails.
constexpr double T = 0x1p-30;
constexpr double HALF = 0.5;
constexpr double NEG = -0x1p-40;
constexpr int32_t K = 3;

//@ ensures result * 1073741824 == 1
double tolerance() {
  return T;
}

//@ ensures result == T
double hexadecimal() {
  return 0x1p-30;
}

//@ ensures result == NEG && result * 1099511627776 == -1
double negative() {
  return NEG;
}

//@ ensures result == K * HALF
double three_halves() {
  return 1.5;
}

// The constant in an operation rounds once.
//@ requires std::isfinite(x) && |x| <= 1
//@ ensures |result - x * T| <= eps * |x * T| + eta
double scaled(double x) {
  return x * T;
}

//@ requires std::isfinite(x) && |x| <= DBL_MAX / 4
//@ ensures |result - 2 * x| <= eps * |2 * x| + eta
double twice(double x) {
  return 2.0 * x;
}
