#include <cstdint>

// Claims through a plain member function that do not hold, decision 0189.
struct Step {
  //@ requires -1000 <= x && x <= 1000
  //@ ensures result == x + 1
  int32_t apply(int32_t x) const { return x + 1; }
};

class Twice {
 public:
  // Two steps add two, not one.
  //@ requires -100 <= x && x <= 100
  //@ ensures result == x + 1
  int32_t run(int32_t x) const { return step_.apply(step_.apply(x)); }

 private:
  Step step_;
};

// Dafny checks the requires line of the function at each call in code.
//@ ensures true
int32_t far(const Step& s) {
  return s.apply(5000) + 0;
}
