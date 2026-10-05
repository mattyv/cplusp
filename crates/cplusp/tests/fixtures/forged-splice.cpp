#include <cstdint>
#\
line 1 "<built-in>" 3
int32_t f(int32_t x) {
  if (x > 0) {
    goto done;
  }
  x = 1;
done:
  return x;
}
