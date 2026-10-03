#include <cstdint>

//@ ensures result == a * b
int64_t product(int32_t a, int32_t b) {
  return int64_t{a} * b;
}
