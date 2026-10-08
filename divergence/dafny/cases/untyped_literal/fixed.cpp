#include <cstdint>

//@ ensures result
bool positive() {
  return int64_t{2147483647} + 1 > 0;
}
