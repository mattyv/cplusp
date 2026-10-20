#include <cstdint>
#include <memory>

// A unique_ptr of an interface, made by std::make_unique of a final class over it, and a call through it, decision 0168.
struct Shape {
  virtual ~Shape() = default;
  virtual bool valid() const = 0;
  //@ requires valid()
  //@ ensures 0 <= result && result <= 1000000
  virtual int32_t area() const = 0;
};

class Square final : public Shape {
 public:
  //@ requires 0 <= side && side <= 1000
  //@ ensures valid() && this->side_ == side
  explicit Square(int32_t side) : side_(side) {}
  //@ ensures result == (0 <= side_ && side_ <= 1000)
  bool valid() const override { return 0 <= side_ && side_ <= 1000; }
  //@ requires valid()
  //@ ensures result == side_ * side_
  int32_t area() const override {
    //@ apply MulBound(side_, side_, 1000, 1000)
    return side_ * side_;
  }

 private:
  int32_t side_;
};

class Unit final : public Shape {
 public:
  //@ ensures result == true
  bool valid() const override { return true; }
  //@ ensures result == 1
  int32_t area() const override { return 1; }
};

//@ requires 0 <= size && size <= 1000
//@ ensures result != nullptr && result->valid()
std::unique_ptr<Shape> make_shape(bool unit, int32_t size) {
  if (unit) {
    return std::make_unique<Unit>();
  }
  return std::make_unique<Square>(size);
}

//@ requires 0 <= size && size <= 1000
//@ ensures 0 <= result && result <= 1000000
int32_t area_of(bool unit, int32_t size) {
  std::unique_ptr<Shape> s = make_shape(unit, size);
  return s->area();
}

//@ requires p != nullptr && p->valid()
//@ ensures result == p->area()
int32_t read(const std::unique_ptr<Shape>& p) {
  return p->area();
}

//@ ensures result == 9
int32_t nine() {
  std::unique_ptr<Shape> s = std::make_unique<Square>(3);
  return read(s);
}

//@ ensures result == 9
int32_t direct() {
  return read(std::make_unique<Square>(3));
}
