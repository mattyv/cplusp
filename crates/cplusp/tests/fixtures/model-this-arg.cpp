#include <cstdint>

// `*this` is the object, as an argument for a const reference or a value, decision 0214.
struct Point {
  int32_t x;
  int32_t y;

  //@ requires -1000 <= x <= 1000 && -1000 <= y <= 1000
  //@ ensures result == x + y
  int32_t sum() const;

  //@ requires -1000 <= x <= 1000
  //@ ensures result == 2 * x
  int32_t twice() const;
};

//@ requires -1000 <= p.x <= 1000 && -1000 <= p.y <= 1000
//@ ensures result == p.x + p.y
int32_t add(const Point& p) {
  return p.x + p.y;
}

//@ requires -1000 <= p.x <= 1000
//@ ensures result == 2 * p.x
int32_t dbl(Point p) {
  return p.x + p.x;
}

int32_t Point::sum() const {
  return add(*this);
}

int32_t Point::twice() const {
  return dbl(*this);
}
