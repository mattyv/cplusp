#include <cstdint>
// An assignment of a call that writes its object proves in each spelling, decision 0225.
class Counter {
 public:
  //@ ensures count_ == 0
  Counter() : count_(0) {}

  //@ requires count_ < 100
  //@ ensures count_ == old(count_) + 1
  //@ ensures result == count_
  int32_t bump() {
    count_ = count_ + 1;
    return count_;
  }

 private:
  int32_t count_;
};

//@ ensures result == 1
int32_t use_plain() {
  Counter c;
  int32_t x = 0;
  x = c.bump();
  return x;
}

//@ ensures result == 1
int32_t use_paren() {
  Counter c;
  int32_t x = 0;
  x = (c.bump());
  return x;
}

//@ ensures result == 1
int32_t use_sum() {
  Counter c;
  int32_t x = 0;
  x = c.bump() + 0;
  return x;
}
