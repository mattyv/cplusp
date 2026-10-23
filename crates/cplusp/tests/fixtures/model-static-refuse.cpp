#include <cstdint>

// A contract that calls a static that writes, a bare static call outside its class, and a static whose contract names a field,
// decision 0174.
struct Tally {
  int32_t n_;

  //@ reads Tally::count_
  //@ ensures result == (0 <= Tally::count_ && Tally::count_ <= 1000)
  static bool valid() { return 0 <= count_ && count_ <= 1000; }

  //@ requires valid() && Tally::count_ < 1000
  //@ modifies Tally::count_
  //@ ensures valid()
  static void bump() { count_ += 1; }

  //@ requires valid() && Tally::count_ < 1000
  //@ modifies Tally::count_
  //@ ensures bump()
  static void bump_twice() { count_ += 1; }

  //@ reads Tally::count_
  //@ ensures result == n_
  static int32_t peek() { return count_; }

  static int32_t count_;
};

int32_t Tally::count_ = 0;

//@ requires valid()
//@ reads Tally::count_
//@ ensures result == Tally::count_
int32_t outside() {
  return Tally::count_;
}
