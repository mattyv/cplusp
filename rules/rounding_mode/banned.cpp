#include <cfenv>

double rounded_up(double a, double b) {
  std::fesetround(FE_UPWARD);  // BANNED
  return a + b;
}

void restore(const std::fenv_t& saved) {
  std::fesetenv(&saved);  // BANNED
}
