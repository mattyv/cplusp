#include <cstdint>

//@ requires counter < 0x7FFFFFFF
//@ modifies counter
//@ ensures counter == old(counter) + 1 && result == counter
int32_t next(int32_t& counter) {
  return ++counter;
}

struct Pair {
  int32_t a;
  int32_t b;

  //@ requires counter <= 0x7FFFFFF0
  //@ modifies counter
  //@ ensures a == old(counter) + 1 && b == old(counter) + 2
  explicit Pair(int32_t& counter) : a(next(counter)), b(next(counter)) {}
};

//@ ensures result.a == 1 && result.b == 2
Pair make() {
  int32_t counter = 0;
  return Pair(counter);
}
