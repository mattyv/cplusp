#include <cstddef>
#include <cstdint>
#include <memory>
#include <vector>

// A vector of unique_ptr of an interface, read through each element, and a local vector built by push_back, decision 0170.
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

class Rect final : public Shape {
 public:
  //@ requires 0 <= w && w <= 1000 && 0 <= h && h <= 1000
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

//@ requires shapes.size() <= 1000
//@ requires forall i :: 0 <= i < shapes.size() ==> shapes[i] != nullptr
//@ requires forall i :: 0 <= i < shapes.size() ==> shapes[i]->valid()
//@ ensures 0 <= result && result <= 1000000000
int64_t total_area(const std::vector<std::unique_ptr<Shape>>& shapes) {
  int64_t total = 0;
  //@ invariant 0 <= i && i <= shapes.size()
  //@ invariant 0 <= total && total <= 1000000 * i
  for (size_t i = 0; i < shapes.size(); ++i) {
    total += shapes[i]->area();
  }
  return total;
}

//@ ensures 0 <= result && result <= 1000000000
int64_t sample_total() {
  std::vector<std::unique_ptr<Shape>> shapes;
  shapes.push_back(std::make_unique<Square>(5));
  shapes.push_back(std::make_unique<Rect>(2, 3));
  return total_area(shapes);
}
