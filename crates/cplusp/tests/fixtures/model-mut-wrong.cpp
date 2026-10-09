#include <cstdint>

// A write that may overflow and an ensures line that does not hold are named at their lines, decision 0096.
struct Counter {
  int32_t n_;

  void bump() {
    n_ += 1;
  }

  //@ ensures n_ == 1
  void reset() {
    n_ = 0;
  }
};
