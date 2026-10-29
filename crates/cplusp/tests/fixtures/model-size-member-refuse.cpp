#include <cstdint>

// The forms of size that have no rule, decision 0200.
struct P {
  int32_t v;
};

// A struct with no member size.
//@ ensures result == p.size()
int32_t f(const P& p) {
  return p.v;
}

// A scalar has no size.
//@ ensures result == x.size()
int32_t g(int32_t x) {
  return x;
}
