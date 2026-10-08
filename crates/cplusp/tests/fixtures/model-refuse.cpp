#include <cstdint>

int32_t one() {
  return 1;
}

//@ ensures result == 1
int32_t call_one() {
  return 7 % 2;
}

//@ ensures result == y
int32_t named(int32_t x) {
  return x;
}
