#include <cstdint>

// A contract that calls a member function that is not pure, or no member function at all, is refused, decision 0090.
struct Counter {
  int32_t n_;

  int32_t copy() const {
    int32_t a = n_;
    return a;
  }
};

//@ ensures result == c.copy()
int32_t first(const Counter& c) {
  return 0;
}

//@ ensures result == c.three()
int32_t second(const Counter& c) {
  return 0;
}

struct Other {
  int32_t n_;

  //@ requires nosuch > 0
  bool refused() const {
    return n_ > 0;
  }
};

//@ ensures result == o.refused()
bool third(const Other& o) {
  return true;
}
