#include <cstdint>
// The override requires more than the interface, and its hint needs that extra bound, decision 0167.
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
