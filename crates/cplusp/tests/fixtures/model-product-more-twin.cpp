#include <cstdint>
// The same override, and a free function whose own hint fails, decision 0167.
struct Shape {
  virtual ~Shape() = default;
  virtual bool valid() const = 0;
  //@ requires valid()
  //@ ensures 0 <= result && result <= 1000000
  virtual int32_t area() const = 0;
};
class Rect final : public Shape {
 public:
  //@ ensures result == (0 <= w_ && w_ <= 1000 && 0 <= h_ && h_ <= 1000)
  bool valid() const override { return 0 <= w_ && w_ <= 1000 && 0 <= h_ && h_ <= 1000; }
  //@ requires valid() && w_ <= 500
  //@ ensures result == w_ * h_
  int32_t area() const override {
    //@ apply MulBound(w_, h_, 500, 1000)
    return w_ * h_;
  }
 private:
  int32_t w_;
  int32_t h_;
};
//@ requires 0 <= x && x <= 2000
//@ ensures result <= 2000000
int32_t scale(int32_t x) {
  //@ apply MulBound(x, x, 1000, 1000)
  return x * x;
}
