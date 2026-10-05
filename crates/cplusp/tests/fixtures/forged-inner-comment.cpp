#include <cstdint>
# /* x */ 1 "pretend-system.hpp" 1 3
int32_t f(int32_t x) {
  if (x > 0) {
    goto done;
  }
  x = 1;
done:
  return x;
}
