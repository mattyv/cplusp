#include <cstdint>

// A chain runs each step in order, so a claim with a step left out fails, and a step whose requires line fails is named, decision
// 0183.
class Counter {
 public:
  //@ ensures total() == 0
  Counter() : total_(0) {}

  //@ requires 0 <= n && n <= 100 && 0 <= total() && total() <= 150
  //@ ensures total() == old(total()) + n
  Counter& add(int32_t n) {
    total_ += n;
    return *this;
  }

  //@ ensures result == total_
  int32_t total() const { return total_; }

 private:
  int32_t total_;
};

//@ ensures result == 3
int32_t forgets() {
  return Counter().add(1).add(1).add(1).add(1).total();
}

//@ ensures result == 300
int32_t too_far() {
  Counter c;
  c.add(100).add(100).add(100);
  return c.total();
}

//@ ensures true
int32_t spread() {
  Counter c;
  c.add(100)
      .add(100)
      .add(100);
  return c.total();
}
