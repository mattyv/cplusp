#include <cstdint>

// A constructor with only a member init list is a method that gives the value it builds, decision 0094.
struct Counter {
  int32_t n_;

  //@ requires 0 <= n && n <= 1000
  //@ ensures valid() && n_ == n
  explicit Counter(int32_t n) : n_(n) {}

  //@ ensures result == (0 <= n_ && n_ <= 1000)
  bool valid() const {
    return 0 <= n_ && n_ <= 1000;
  }
};

//@ ensures result == 7
int32_t make() {
  Counter c(7);
  return c.n_;
}

//@ ensures result.valid() && result.n_ == 3
Counter build() {
  return Counter(3);
}
