#include <cstdint>

//@ ensures result == n
double widen(int64_t n) {
  return static_cast<double>(n);
}
