#include <cstdint>

// The arguments of a member function in a contract pass as the types of its parameters, decision 0095.
struct Counter {
  int32_t n_;

  //@ ensures result == (n_ <= k)
  bool le(int32_t k) const {
    return n_ <= k;
  }

  //@ requires n_ < 1000
  //@ ensures result == n_ + 1
  int32_t inc() const {
    return n_ + 1;
  }
};

//@ requires c.le(k)
//@ ensures result == c.le(k)
bool use_le(const Counter& c, int32_t k) {
  bool b = c.le(k);
  return b;
}

//@ requires c.n_ < 1000
//@ ensures result == c.inc() && c.le(result)
int32_t use_inc(const Counter& c) {
  int32_t r = c.inc();
  return r;
}
