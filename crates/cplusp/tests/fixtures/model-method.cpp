#include <cstdint>

// const member functions, with the object as a parameter this by value, and a private field, decision 0089 steps 1 and 2.
struct Counter {
  int32_t n_;

  //@ requires n_ < 1000
  //@ ensures result == n_ + 1
  int32_t next() const {
    return n_ + 1;
  }

  //@ ensures result == n_
  int32_t value() const {
    return n_;
  }

  //@ requires n_ < 1000
  //@ ensures result == n_ + 1
  int32_t again() const {
    int32_t v = value();
    return v + 1;
  }

  //@ requires n < 1000
  //@ ensures result == n + 1
  int32_t shadow(int32_t n) const {
    return n + 1;
  }

 private:
  int32_t hidden_;
};

//@ requires c.n_ < 1000
//@ ensures result == c.n_ + 1
int32_t bump(const Counter& c) {
  int32_t r = c.next();
  return r;
}
