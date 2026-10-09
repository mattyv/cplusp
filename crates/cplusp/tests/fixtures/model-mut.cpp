#include <cstdint>

// A member function that writes its object takes it in and gives it back, decision 0096.
struct Counter {
  int32_t n_;

  //@ requires n_ < 1000
  //@ ensures n_ == old(n_) + 1
  void bump() {
    n_ += 1;
  }

  //@ ensures n_ == v
  void assign(int32_t v) {
    n_ = v;
  }

  //@ ensures result == old(n_) && n_ == 0
  int32_t take() {
    int32_t v = n_;
    n_ = 0;
    return v;
  }
};

//@ ensures result == 7
int32_t twice() {
  Counter c{5};
  c.bump();
  c.bump();
  int32_t r = c.take();
  return r;
}

//@ requires x < 1000
//@ ensures result == x + 1
int32_t local_compound(int32_t x) {
  int32_t y = x;
  y += 1;
  return y;
}

void nothing() {
  return;
}

//@ ensures result == 3
int32_t calls_void() {
  nothing();
  return 3;
}
