#include <cstdint>

// A member function that lists a global, and a global of a type with no rule, decision 0173.
int32_t total = 0;
double scale = 1.0;

struct Counter {
  int32_t n_;
  //@ modifies total
  void bump() { total += 1; }
};

//@ reads scale
//@ ensures result == 0
int32_t first() {
  return 0;
}

//@ reads x
//@ ensures result == x
int32_t same(int32_t x) {
  return x;
}
