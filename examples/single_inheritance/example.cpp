#include <cstdint>

// One base, virtual functions, override and final. The prover checks each override against the base contract. A derived
// class keeps every promise of the base and may make a stronger one. The base has a virtual destructor.
class Shape {
 public:
  virtual ~Shape() = default;
  //@ ensures result >= 3
  virtual int32_t corners() const = 0;
};

class Square final : public Shape {
 public:
  //@ ensures result == 4
  int32_t corners() const override { return 4; }
};

//@ ensures result >= 3
int32_t count_corners(const Shape& s) {
  return s.corners();
}

//@ ensures result == 4
int32_t square_corners(const Square& q) {
  return q.corners();
}
