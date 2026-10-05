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

// RAII. A guard acquires a handle in its constructor and releases it in its destructor, at the end of the block that owns
// it. The guard owns a value and holds no reference, decision 0029. The pool is a global the contracts list.
int32_t open_handles = 0;

//@ requires 0 <= open_handles < 1000
//@ modifies open_handles
//@ ensures open_handles == old(open_handles) + 1 && result == old(open_handles)
int32_t acquire() {
  return open_handles++;
}

//@ requires open_handles > 0
//@ modifies open_handles
//@ ensures open_handles == old(open_handles) - 1
void release(int32_t) {
  open_handles -= 1;
}

class Guard {
 public:
  //@ requires 0 <= open_handles < 1000
  //@ modifies open_handles
  //@ ensures open_handles == old(open_handles) + 1 && handle() == old(open_handles)
  Guard() : handle_(acquire()) {}

  //@ requires open_handles > 0
  //@ modifies open_handles
  //@ ensures open_handles == old(open_handles) - 1
  ~Guard() { release(handle_); }

  //@ ensures result == handle_
  int32_t handle() const { return handle_; }

 private:
  int32_t handle_;
};

//@ requires 0 <= open_handles < 1000
//@ modifies open_handles
//@ ensures open_handles == old(open_handles) && result == old(open_handles)
int32_t use_one() {
  Guard g;
  return g.handle();
}
