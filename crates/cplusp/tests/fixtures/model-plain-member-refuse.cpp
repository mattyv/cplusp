#include <cstdint>

// Calls that keep the rules of 0104 and 0172, decision 0189.

// A member function whose body holds a call is no plain member function.
struct Deep {
  //@ ensures result == 1
  int32_t one() const { return 1; }

  //@ ensures result == 1
  int32_t again() const { return one(); }
};

struct Top {
  Deep d;

  //@ ensures result == 1
  int32_t top() const { return d.again(); }
};

//@ requires t.top() == 1
//@ ensures result == 1
int32_t use_top(const Top& t) {
  return 1;
}

// A plain member function whose contract has no model stays a method.
struct Odd {
  int32_t v = 0;

  //@ ensures result == v &&& 1
  int32_t get() const { return v; }
};

//@ ensures result == o.v
int32_t use_odd(const Odd& o) {
  return o.get() + 0;
}
