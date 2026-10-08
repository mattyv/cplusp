#include <cstdint>

int32_t one() {
  return 1;
}

//@ ensures result == 1
int32_t call_one() {
  return one();
}

//@ ensures result == y
int32_t named(int32_t x) {
  return x;
}
