#include <cstdint>

// The bound of a product of two names, from the lemma MulBound of the prelude, decision 0167.
struct Shape {
  virtual ~Shape() = default;
  virtual bool valid() const = 0;
  //@ requires valid()
  //@ ensures 0 <= result && result <= 1000000
  virtual int32_t area() const = 0;
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

//@ requires 0 <= x && x <= 1000 && 0 <= k && k <= 1000
//@ ensures 0 <= result && result <= 1000000
int32_t scale(int32_t x, int32_t k) {
  //@ apply MulBound(x, k, 1000, 1000)
  return x * k;
}

//@ ensures result == 12
int32_t demo() {
  const Rect r(3, 4);
  return r.area();
}
