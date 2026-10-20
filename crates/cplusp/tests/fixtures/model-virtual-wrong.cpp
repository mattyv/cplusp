#include <cstdint>

// Two overrides that break the contract of Shape::corners, decision 0165.
class Shape {
 public:
  virtual ~Shape() = default;
  //@ requires 0 <= scale && scale <= 100
  //@ ensures result >= 3 * scale
  virtual int32_t corners(int32_t scale) const = 0;
};

// Requires more than Shape::corners.
class Thin final : public Shape {
 public:
  //@ requires 0 <= s && s <= 10
  //@ ensures result == 4 * s
  int32_t corners(int32_t s) const override { return 4 * s; }
};

// Promises less than Shape::corners.
class Flat final : public Shape {
 public:
  //@ requires 0 <= s && s <= 100
  //@ ensures result == 2 * s
  int32_t corners(int32_t s) const override { return 2 * s; }
};

class Colored {
 public:
  virtual ~Colored() = default;
  //@ ensures 0 <= result && result <= 255
  virtual int32_t red() const = 0;
};

// Keeps the contract of Shape::corners and breaks the one of Colored::red.
class Loud final : public Shape, public Colored {
 public:
  //@ requires 0 <= s && s <= 100
  //@ ensures result == 3 * s
  int32_t corners(int32_t s) const override { return 3 * s; }
  //@ ensures result == 300
  int32_t red() const override { return 300; }
};
