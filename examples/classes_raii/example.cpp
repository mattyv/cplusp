#include <cstdint>

// A class of values. The constructor sets the invariant and each method keeps it, and the prover checks both. The members
// clean themselves up, so the class needs no destructor. A local object is destroyed at the end of its block.
class Counter {
 public:
  //@ requires 0 <= start <= 1000
  //@ ensures value() == start
  explicit Counter(int32_t start) : n_(start) {}

  //@ requires value() < 1000
  //@ modifies this
  //@ ensures value() == old(value()) + 1
  void bump() { n_ += 1; }

  int32_t value() const { return n_; }

 private:
  //@ invariant 0 <= n_ <= 1000
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
