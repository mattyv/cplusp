#include <cstdint>

int32_t total = 0;

int32_t a_write() {
  total += 1;
  return total;
}

int32_t b_write() {
  total += 2;
  return total;
}

int32_t add(int32_t a, int32_t b) {
  return a + b;
}

// Two callees that write a global in their bodies, with no line to say so. Two changes, whatever the state row says.
int32_t both() {
  return add(a_write(), b_write());
}

struct Clock {
  virtual ~Clock() = default;
  virtual int32_t tick() const {
    return 0;
  }
};

struct Loud : Clock {
  int32_t tick() const override {
    total += 1;
    return total;
  }
};

// Two calls of a const virtual function. The function the source names changes nothing, and an override of it writes a global.
int32_t twice(const Clock& c) {
  return add(c.tick(), c.tick());
}
