#include <cstdint>
// A bare call of a name that two member functions share is no pure function, decision 0225.
struct S {
  int32_t a;

  //@ ensures result == 1
  int32_t get(int32_t x) const { return 1; }

  //@ ensures result == 2
  int32_t get(int64_t x) const { return 2; }

  //@ ensures result == get(x)
  int32_t mine(int32_t x) const { return get(x); }
};
