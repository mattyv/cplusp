#include <cstdint>

extern int32_t base_value;

int32_t derived = base_value + 1;

//@ ensures result == base_value + 1
int32_t read_derived() {
  return derived;
}
