#include <cstdint>
#include "../../../../include/cplusp.h"

// A call in code of a member function of the base keeps the contract of that function, decision 0203.
struct P {
  int32_t x;
  //@ requires x < 100
  //@ ensures result == x + 1
  int32_t next() const {
    int32_t y = x;
    return y + 1;
  }
  //@ ensures result == x
  int32_t get() const { return x; }
  //@ ensures result == x + k
  int64_t get(int32_t k) const { return int64_t{x} + k; }
  CPLUSP_TRUSTED("reads x")
  //@ requires x < 100
  //@ ensures result == x + 2
  int32_t skip() const { return x + 2; }
};

struct Q : P {
  int32_t y;
};

//@ ensures result == 2
int32_t one_next() {
  Q a{{1}, 2};
  return a.next();
}

//@ ensures result == 8
int64_t both_gets() {
  Q a{{3}, 2};
  return a.get() + a.get(2);
}

//@ ensures result == 3
int32_t one_skip() {
  Q a{{1}, 2};
  return a.skip();
}
