#include <cstdint>

// A destructor that releases nothing, and a caller that forgets that the guard dies, decision 0178.
int32_t open_handles = 0;

//@ requires 0 <= open_handles < 1000
//@ modifies open_handles
//@ ensures open_handles == old(open_handles) + 1 && result == old(open_handles)
int32_t acquire() {
  return open_handles++;
}

class Guard {
 public:
  //@ requires 0 <= open_handles < 1000
  //@ modifies open_handles
  //@ ensures open_handles == old(open_handles) + 1 && handle() == old(open_handles)
  Guard() : handle_(acquire()) {}

  //@ requires open_handles > 0
  //@ modifies open_handles
  //@ ensures open_handles == old(open_handles) - 1
  ~Guard() {}

  //@ ensures result == handle_
  int32_t handle() const { return handle_; }

 private:
  int32_t handle_;
};

//@ requires 0 <= open_handles < 1000
//@ modifies open_handles
//@ ensures open_handles == old(open_handles) + 1 && result == old(open_handles)
int32_t use_one() {
  Guard g;
  return g.handle();
}

// The count is back before the guard dies, so the requires line of its destructor may not hold, decision 0178.
//@ requires 0 <= open_handles < 1000
//@ modifies open_handles
//@ ensures true
void release_early() {
  Guard g;
  open_handles -= 1;
}
