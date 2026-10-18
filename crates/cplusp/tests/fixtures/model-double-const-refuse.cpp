#include <cmath>

// A constant of a namespace hides the double constant of the file, and a double that the model cannot write exactly is refused,
// in code and in a contract, decision 0158.
constexpr double T = 0x1p-30;
constexpr double TINY = 0x1p-70;

namespace inner {
constexpr double T = 0.25;

//@ ensures result == T
double tolerance() {
  return 0.25;
}
}  // namespace inner

//@ ensures result >= 0.0
double tiny() {
  return 0x1p-70;
}

//@ ensures result >= 0.0
double tiny_constant() {
  return TINY;
}

//@ ensures result == TINY
double tiny_contract() {
  return 0.0;
}
