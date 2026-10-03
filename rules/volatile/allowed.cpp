#include <cstdint>
int32_t read_twice(const int32_t* reg) {
  return *reg + *reg;
}

int32_t local() {
  int32_t v = 1;
  return v;
}
