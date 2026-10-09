#include <cstdint>

// The conditional operator in code and in contracts, and a struct with an operator(), decision 0098.
struct CapAt {
  int32_t limit;

  //@ ensures result == (x < limit ? x : limit)
  int32_t operator()(int32_t x) const { return x < limit ? x : limit; }
};

//@ ensures result == (x < 0 ? -x : x)
//@ ensures result >= 0
int64_t magnitude(int32_t x) {
  return x < 0 ? -int64_t{x} : int64_t{x};
}

//@ ensures result == (x < c.limit ? x : c.limit)
int32_t cap_once(CapAt c, int32_t x) {
  return c(x);
}

//@ ensures result == c(c(x))
int32_t cap_twice(CapAt c, int32_t x) {
  int32_t y = c(x);
  int32_t z = c(y);
  return z;
}

//@ ensures result == (b ? 1 : 0)
int32_t to_int(bool b) {
  if (b) {
    return 1;
  }
  return 0;
}

// A functor that is not idempotent, so a contract with two calls differs from one with one call, decision 0100.
struct AddOne {
  //@ requires x < 1000
  //@ ensures result == x + 1
  int32_t operator()(int32_t x) const { return x + 1; }
};

//@ requires x < 500
//@ ensures result == a(a(x))
int32_t add_two(AddOne a, int32_t x) {
  int32_t y = a(x);
  int32_t z = a(y);
  return z;
}
