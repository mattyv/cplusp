#include <cstdint>

// A contract that calls a member function outside its requires lines is named at the contract line, decision 0095.
struct Counter {
  int32_t n_;

  //@ requires n_ < 1000
  //@ ensures result == n_ + 1
  int32_t inc() const {
    return n_ + 1;
  }
};

//@ ensures result == c.inc()
int32_t take(const Counter& c) {
  return 0;
}
