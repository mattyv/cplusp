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

#include <algorithm>
#include <vector>

bool any_and(bool a, bool b) {
  return a && b;
}

// Two lambdas that each call a writer with no line. The std call runs the lambda, and the lambda runs the writer.
bool two_lambdas(const std::vector<int32_t>& v) {
  return any_and(std::ranges::any_of(v, [](int32_t x) { return a_write() > x; }), std::ranges::any_of(v, [](int32_t x) { return b_write() > x; }));
}

struct Copied {
  int32_t v = 0;
  Copied() = default;
  Copied(const Copied& other) : v(other.v) {
    total += 1;
  }
};

bool both_empty(std::vector<Copied> a, std::vector<Copied> b) {
  return a.empty() && b.empty();
}

// Two copies of a container, and the element's copy constructor writes with no line.
bool copied_twice(const std::vector<Copied>& v) {
  return both_empty(v, v);
}
