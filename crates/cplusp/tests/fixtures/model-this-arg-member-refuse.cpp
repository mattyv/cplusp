#include <cstdint>

// `*this` as a reference that is not const has no rule yet, in a member call too, decisions 0214 and 0217.
struct Wiper;

struct Point {
  int32_t x;

  //@ ensures true
  void clear(const Wiper& w);
};

struct Wiper {
  int32_t n;

  //@ modifies p
  //@ ensures p.x == 0
  void wipe(Point& p) const { p.x = 0; }
};

void Point::clear(const Wiper& w) {
  w.wipe(*this);
}
