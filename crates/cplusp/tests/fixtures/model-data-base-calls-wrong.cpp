#include <cstdint>

// A false claim on a call of a member function of the base fails, decision 0203.
struct P {
  int32_t x;
  //@ requires x < 100
  //@ ensures result == x + 1
  int32_t next() const {
    int32_t y = x;
    return y + 1;
  }
};

struct Q : P {
  int32_t y;
};

//@ ensures result == 3
int32_t one_next() {
  Q a{{1}, 2};
  return a.next();
}

//@ ensures true
int32_t too_big() {
  Q a{{100}, 2};
  return a.next();
}
