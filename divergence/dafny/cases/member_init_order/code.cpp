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
  //@ ensures b == old(counter) + 1 && a == old(counter) + 2
  explicit Pair(int32_t& counter) : b(next(counter)), a(next(counter)) {}
};

//@ ensures result.b == 1 && result.a == 2
Pair make() {
  int32_t counter = 0;
  return Pair(counter);
}
