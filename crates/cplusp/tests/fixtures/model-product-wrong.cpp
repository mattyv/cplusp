#include <cstdint>

// A bound of a product that the requires lines do not give, decision 0167.
//@ requires 0 <= x && x <= 2000 && 0 <= k && k <= 1000
//@ ensures result <= 2000000
int32_t scale(int32_t x, int32_t k) {
  //@ apply MulBound(x, k, 1000, 1000)
  return x * k;
}

struct Shape {
  virtual ~Shape() = default;
  virtual bool valid() const = 0;
  //@ requires valid()
  //@ ensures 0 <= result && result <= 1000000
  virtual int32_t area() const = 0;
};

// A bound below the one that valid() gives, in a pure override.
class Rect final : public Shape {
 public:
  //@ ensures result == (0 <= w_ && w_ <= 1000 && 0 <= h_ && h_ <= 1000)
  bool valid() const override { return 0 <= w_ && w_ <= 1000 && 0 <= h_ && h_ <= 1000; }
  //@ requires valid()
  //@ ensures result == w_ * h_
  int32_t area() const override {
    //@ apply MulBound(w_, h_, 100, 100)
    return w_ * h_;
  }

 private:
  int32_t w_;
  int32_t h_;
};
