#include <cstdint>

//@ ensures result
bool positive() {
  return 2147483647 + 1 > 0;
}
