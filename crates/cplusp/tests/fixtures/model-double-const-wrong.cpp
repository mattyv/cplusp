#include <cmath>

// A whole number next to a real does not make a wrong contract hold, decision 0158.
constexpr double T = 0x1p-30;

//@ ensures result == 2 * T
double tolerance() {
  return T;
}

//@ ensures result * 1073741824 == 2
double hexadecimal() {
  return 0x1p-30;
}
