#include <cstdint>

// `*this` as a reference that is not const has no rule yet, decision 0214.
struct Point {
  int32_t x;

  //@ ensures true
  void clear();
};

//@ modifies p
//@ ensures p.x == 0
void reset(Point& p) {
  p.x = 0;
}

void Point::clear() {
  reset(*this);
}
