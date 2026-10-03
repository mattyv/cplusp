#include <cfenv>
#include <cstdint>

double plain_sum(double a, double b) {
  return a + b;
}

int32_t mode() {
  return std::fegetround();
}
