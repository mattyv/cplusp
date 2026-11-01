#include <cstdint>
// A conditional of two locals with destructors is a copy, so a return of it is refused, decision 0225.
int32_t open_handles = 0;

class Guard {
 public:
  //@ ensures true
  Guard() : handle_(0) {}

  //@ requires open_handles > 0
  //@ modifies open_handles
  //@ ensures open_handles == old(open_handles) - 1
  ~Guard() { open_handles -= 1; }

 private:
  int32_t handle_;
};

//@ requires open_handles > 1
//@ modifies open_handles
//@ ensures open_handles == old(open_handles) - 2
Guard pick(bool c) {
  Guard a;
  Guard b;
  return c ? a : b;
}
