#include <cstdint>

// A class of values. The invariant is the predicate valid(), decision 0028. The constructor establishes it and each method
// requires and ensures it. Members are in scope by name and are never listed. The members clean themselves up, so this
// class needs no destructor. A local object is destroyed at the end of its block.
class Counter {
 public:
  //@ requires 0 <= start <= 1000
  //@ ensures valid() && value() == start
  explicit Counter(int32_t start) : n_(start) {}

  //@ ensures result == (0 <= n_ && n_ <= 1000)
  bool valid() const { return 0 <= n_ && n_ <= 1000; }

  //@ requires valid() && value() < 1000
  //@ ensures valid() && value() == old(value()) + 1
  void bump() { n_ += 1; }

  //@ ensures result == n_
  int32_t value() const { return n_; }

 private:
  int32_t n_;
};

//@ requires 0 <= start <= 998
//@ ensures result == start + 2
int32_t bumped_twice(int32_t start) {
  Counter c(start);
  c.bump();
  c.bump();
  return c.value();
}

// A destructor runs at the end of the block that owns the object, and it gives back what the constructor took. The guard sets a flag
// while it lives. The model has no destructor, so it calls Destroy by hand at the end of the block.
class Guard {
 public:
  //@ modifies flag
  //@ ensures flag == 1
  explicit Guard(int32_t& flag) : flag_(flag) { flag_ = 1; }

  //@ ensures flag_ == 0
  ~Guard() { flag_ = 0; }

 private:
  int32_t& flag_;
};

//@ modifies busy
//@ ensures result == 1 && busy == 0
int32_t run(int32_t& busy) {
  Guard g(busy);
  return busy;
}
