#include <cstdint>
#include <memory>

// A unique_ptr of an interface that may be null, and one that may not be valid, decision 0168.
struct Shape {
  virtual ~Shape() = default;
  virtual bool valid() const = 0;
  //@ requires valid()
  //@ ensures 0 <= result && result <= 1000000
  virtual int32_t area() const = 0;
};

//@ requires p == nullptr || p->valid()
//@ ensures result >= 0
int32_t maybe(const std::unique_ptr<Shape>& p) {
  return p->area();
}

//@ requires p != nullptr
//@ ensures result >= 0
int32_t unchecked(const std::unique_ptr<Shape>& p) {
  return p->area();
}
