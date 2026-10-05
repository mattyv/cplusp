#include <cstdint>
#include <memory>
#include <utility>

// Type erasure. Plain structs have no base class and share no interface, and a wrapper holds any one of them behind a private
// interface. Concept is that interface. Model<T> is a class template that derives from it and forwards to a T. Shape owns a
// Concept and is made from any T by a constructor template.
// The classic wrapper has an implicit constructor, `template <typename T> Shape(T value)`, so that `Shape s = Square{3}` works.
// The gate refuses it at that line: "Implicit conversions (non-`explicit` ctors, conversion operators): not allowed in verified
// code. Hidden calls confuse contracts. Use explicit on the constructor or conversion operator." The constructor template is
// otherwise allowed, because it has type parameters only. So the constructor here is `explicit`, and a caller writes `Shape s(Square{3})`.
struct Concept {
  virtual ~Concept() = default;
  // The invariant of each wrapped value, decision 0028. The interface cannot know the fields, so it is virtual.
  virtual bool valid() const = 0;
  //@ requires valid()
  //@ ensures 0 <= result <= 1000000
  virtual int32_t area() const = 0;
};

// The template is verified once for each T it is used at, and each instantiation forwards a contract that T keeps.
template <typename T>
class Model final : public Concept {
 public:
  //@ requires value.valid()
  //@ ensures valid()
  explicit Model(T value) : value_(std::move(value)) {}

  //@ ensures result == value_.valid()
  bool valid() const override { return value_.valid(); }

  //@ requires valid()
  //@ ensures result == value_.area()
  int32_t area() const override { return value_.area(); }

 private:
  T value_;
};

class Shape {
 public:
  //@ requires value.valid()
  //@ ensures valid()
  template <typename T>
  explicit Shape(T value) : self_(std::make_unique<Model<T>>(std::move(value))) {}

  //@ ensures result == (self_ != nullptr && self_->valid())
  bool valid() const { return self_ != nullptr && self_->valid(); }

  //@ requires valid()
  //@ ensures 0 <= result <= 1000000
  int32_t area() const { return self_->area(); }

 private:
  std::unique_ptr<Concept> self_;
};

// Two plain structs. They name no base class, and each has the two functions that Model<T> forwards to.
struct Square {
  int32_t side;

  //@ ensures result == (0 <= side && side <= 1000)
  bool valid() const { return 0 <= side && side <= 1000; }

  //@ requires valid()
  //@ ensures 0 <= result <= 1000000 && result == side * side
  int32_t area() const { return side * side; }
};

struct Rect {
  int32_t w;
  int32_t h;

  //@ ensures result == (0 <= w && w <= 1000 && 0 <= h && h <= 1000)
  bool valid() const { return 0 <= w && w <= 1000 && 0 <= h && h <= 1000; }

  //@ requires valid()
  //@ ensures 0 <= result <= 1000000 && result == w * h
  int32_t area() const { return w * h; }
};

//@ requires 0 <= side <= 1000 && 0 <= w <= 1000 && 0 <= h <= 1000
//@ ensures 0 <= result <= 2000000
int32_t two_shapes(int32_t side, int32_t w, int32_t h) {
  const Shape a(Square{side});
  const Shape b(Rect{w, h});
  return a.area() + b.area();
}
