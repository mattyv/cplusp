#include <cstdint>
#include <memory>

// A factory returns an owning pointer to an interface and the caller never learns the class. The interface has a contract and
// each class makes it precise. The factory promises a shape that is valid, and the caller proves its area bound from the interface
// contract alone. It holds for every class the factory may build, now and later.
enum class Kind : uint8_t { Square, Rect };

struct Shape {
  virtual ~Shape() = default;
  // The invariant of each shape, decision 0028. The interface cannot know the fields, so it is virtual.
  virtual bool valid() const = 0;
  //@ requires valid()
  //@ ensures 0 <= result <= 1000000
  virtual int32_t area() const = 0;
};

class Square final : public Shape {
 public:
  //@ requires 0 <= side <= 1000
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

class Rect final : public Shape {
 public:
  //@ requires 0 <= w <= 1000 && 0 <= h <= 1000
  //@ ensures valid() && this->w_ == w && this->h_ == h
  Rect(int32_t w, int32_t h) : w_(w), h_(h) {}

  //@ ensures result == (0 <= w_ && w_ <= 1000 && 0 <= h_ && h_ <= 1000)
  bool valid() const override { return 0 <= w_ && w_ <= 1000 && 0 <= h_ && h_ <= 1000; }

  //@ requires valid()
  //@ ensures result == w_ * h_
  int32_t area() const override {
    //@ apply MulBound(w_, h_, 1000, 1000)
    return w_ * h_;
  }

 private:
  int32_t w_;
  int32_t h_;
};

// The factory. A Square is size by size, and a Rect is size by 2.
//@ requires 0 <= size <= 1000
//@ ensures result != nullptr && result->valid()
std::unique_ptr<Shape> make_shape(Kind k, int32_t size) {
  if (k == Kind::Square) {
    return std::make_unique<Square>(size);
  }
  return std::make_unique<Rect>(size, 2);
}

//@ requires 0 <= size <= 1000
//@ ensures 0 <= result <= 1000000
int32_t area_of(Kind k, int32_t size) {
  std::unique_ptr<Shape> s = make_shape(k, size);
  return s->area();
}
