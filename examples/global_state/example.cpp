#include <cstdint>

// A global is an input and an output of every function that touches it, and the contract lists it. A function that changes the
// global says so in `modifies`, and a function that only reads it says so in `reads`. A caller then knows what a call can change.
// A static data member is a global with a class name, and the contract names it in the same way.
int32_t total = 0;

//@ requires -0x40000000 <= x < 0x40000000
//@ requires -0x40000000 <= total < 0x40000000
//@ modifies total
//@ ensures total == old(total) + x
void add(int32_t x) {
  total += x;
}

//@ reads total
//@ ensures result == total
int32_t current() {
  return total;
}

//@ requires -0x20000000 <= x < 0x20000000
//@ requires -0x20000000 <= total < 0x20000000
//@ modifies total
//@ ensures total == old(total) + 2 * x
void add_twice(int32_t x) {
  add(x);
  add(x);
}

struct Registry {
  static int32_t last_id;
};

int32_t Registry::last_id = 0;

//@ requires Registry::last_id < 0x7FFFFFFF
//@ modifies Registry::last_id
//@ ensures Registry::last_id == old(Registry::last_id) + 1
//@ ensures result == Registry::last_id
int32_t next_id() {
  Registry::last_id += 1;
  return Registry::last_id;
}
