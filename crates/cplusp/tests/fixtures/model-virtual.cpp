#include <cstdint>

// An interface, a final class over it, and a call through const Shape&, decision 0165. The override requires less and promises more.
class Shape {
 public:
  virtual ~Shape() = default;
  //@ requires 0 <= scale && scale <= 100
  //@ ensures result >= 3 * scale
  virtual int32_t corners(int32_t scale) const = 0;
};

class Square final : public Shape {
 public:
  //@ requires 0 <= s && s <= 1000
  //@ ensures result == 4 * s
  int32_t corners(int32_t s) const override { return 4 * s; }
};

//@ ensures result >= 3
int32_t count(const Shape& shape) {
  return shape.corners(1);
}

//@ ensures result == 8
int32_t square(const Square& q) {
  return q.corners(2);
}
