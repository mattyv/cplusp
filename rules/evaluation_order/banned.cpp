#include <cstdint>

//@ requires x < 0x7FFFFFFF
int32_t next(int32_t& x) {
  return x++;
}

bool before(int32_t a, int32_t b) {
  return a < b;
}

struct Counter {
  int32_t n = 0;
  int32_t bump() { return n++; }
};

bool rises(int32_t& x) {
  return before(next(x), next(x));  // BANNED
}

int32_t both(int32_t& x, int32_t& y) {
  return next(x) + next(y);  // BANNED
}

int32_t twice_bumped(Counter& c) {
  return c.bump() + c.bump();  // BANNED
}

int32_t unsequenced(int32_t& x) {
  return x++ - x++;  // BANNED
}

#include <utility>

bool mixed(int32_t& x) {
  return before(next(x), x++);  // BANNED
}

bool exchanged(int32_t& x) {
  return before(std::exchange(x, 1), std::exchange(x, 2));  // BANNED
}
