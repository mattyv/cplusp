#include <cstdint>

// A plain member function can hold apply lines, decision 0211.
struct Square {
  int32_t side;

  //@ ensures result == (0 <= side && side <= 1000)
  bool valid() const { return 0 <= side && side <= 1000; }

  //@ requires valid()
  //@ ensures 0 <= result <= 1000000 && result == side * side
  int32_t area() const {
    //@ apply MulBound(side, side, 1000, 1000)
    return side * side;
  }
};

struct Frame {
  Square inner;

  //@ requires inner.valid()
  //@ ensures result == inner.area() + 1
  int32_t padded() const { return inner.area() + 1; }
};

//@ requires f.inner.valid()
//@ ensures 1 <= result <= 1000001 && result == f.padded()
int32_t pad_of(const Frame& f) {
  return f.padded();
}
