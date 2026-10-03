#include <cstdint>

extern int32_t base_value;

int32_t derived_value() {
  return base_value + 1;
}

//@ requires base_value < 0x7FFFFFFF
//@ ensures result == base_value + 1
int32_t read_derived() {
  return derived_value();
}
