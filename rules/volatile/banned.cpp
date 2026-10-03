#include <cstdint>
int32_t read_twice(volatile int32_t* reg) {  // BANNED
  return *reg + *reg;
}

int32_t read_ref(volatile int32_t& reg) {  // BANNED
  return reg;
}

int32_t local() {
  volatile int32_t v = 1;  // BANNED
  return v;
}

struct Device {
  volatile int32_t status = 0;  // BANNED
};
