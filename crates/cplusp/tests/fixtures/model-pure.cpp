#include <cstdint>

// A pure const member function is also a Dafny function that contracts can call, decision 0090.
struct Counter {
  int32_t n_;

  //@ ensures result == (0 <= n_ && n_ <= 1000)
  bool valid() const {
    return 0 <= n_ && n_ <= 1000;
  }

  //@ requires valid() && n_ < 1000
  //@ ensures result == n_ + 1
  int32_t next() const {
    return n_ + 1;
  }
};

//@ requires c.valid() && c.n_ < 1000
//@ ensures result == c.next()
int32_t bump(const Counter& c) {
  int32_t r = c.next();
  return r;
}

//@ requires c.valid()
//@ ensures result
bool check(const Counter& c) {
  bool v = c.valid();
  return v;
}
