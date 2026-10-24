#include <cstdint>

// A fluent builder. Each step sets one field and returns the builder, so the calls chain in one expression. The object of a member
// call is evaluated before its arguments, and a call whose result is the object of the next call comes before it, so the standard
// orders the three steps and the gate takes the chain. The result of a step is the builder itself. Each step ends in
// `return *this;`, so the translator knows it and the contract need not say it, decision 0183. The classic form passes the gate as it is.
struct Config {
  int32_t width;
  int32_t height;
  int32_t depth;
};

class Builder {
 public:
  //@ ensures valid() && width_ == 0 && height_ == 0 && depth_ == 0
  Builder() : width_(0), height_(0), depth_(0) {}

  //@ ensures result == (0 <= width_ && width_ <= 1000 && 0 <= height_ && height_ <= 1000 && 0 <= depth_ && depth_ <= 1000)
  bool valid() const { return 0 <= width_ && width_ <= 1000 && 0 <= height_ && height_ <= 1000 && 0 <= depth_ && depth_ <= 1000; }

  //@ requires valid() && 0 <= w <= 1000
  //@ ensures valid() && width_ == w && height_ == old(height_) && depth_ == old(depth_)
  Builder& width(int32_t w) {
    width_ = w;
    return *this;
  }

  //@ requires valid() && 0 <= h <= 1000
  //@ ensures valid() && height_ == h && width_ == old(width_) && depth_ == old(depth_)
  Builder& height(int32_t h) {
    height_ = h;
    return *this;
  }

  //@ requires valid() && 0 <= d <= 1000
  //@ ensures valid() && depth_ == d && width_ == old(width_) && height_ == old(height_)
  Builder& depth(int32_t d) {
    depth_ = d;
    return *this;
  }

  //@ requires valid()
  //@ ensures result.width == width_ && result.height == height_ && result.depth == depth_
  Config build() const { return Config{width_, height_, depth_}; }

 private:
  int32_t width_;
  int32_t height_;
  int32_t depth_;
};

//@ ensures result.width == 10 && result.height == 20 && result.depth == 30
Config make_box() {
  return Builder().width(10).height(20).depth(30).build();
}

// Two steps and a default. The step that is left out keeps the value the constructor gave.
//@ ensures result.width == 7 && result.height == 0 && result.depth == 9
Config make_flat() {
  Builder b;
  b.depth(9).width(7);
  return b.build();
}
