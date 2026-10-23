#include <cstddef>
#include <cstdint>
#include "../../../../include/cplusp.h"

// A bump that adds two, a call too few, an ensures line that calls used() before valid(), and a caller that does not meet a
// requires line of a trusted static, decision 0174.
class Tally {
 public:
  Tally() = delete;

  //@ reads Tally::count_
  //@ ensures result == (0 <= Tally::count_ && Tally::count_ <= 1000)
  static bool valid() { return 0 <= count_ && count_ <= 1000; }

  //@ requires valid()
  //@ reads Tally::count_
  //@ ensures result == Tally::count_
  static int32_t count() { return count_; }

  //@ requires valid() && count() < 999
  //@ modifies Tally::count_
  //@ ensures valid() && count() == old(count()) + 1
  static void bump() { count_ += 2; }

  //@ requires valid() && count() < 1000
  //@ modifies Tally::count_
  //@ ensures valid() && count() == old(count()) + 1
  static void bump_right() { count_ += 1; }

 private:
  static int32_t count_;
};

int32_t Tally::count_ = 0;

//@ requires Tally::valid() && Tally::count() <= 997
//@ modifies Tally::count_
//@ ensures Tally::valid() && Tally::count() == old(Tally::count()) + 3
void three_bumps() {
  Tally::bump_right();
  Tally::bump_right();
}

class Pool {
 public:
  Pool() = delete;

  //@ reads Pool::used_
  //@ ensures result == (Pool::used_ <= 4096)
  static bool valid() { return used_ <= 4096; }

  //@ requires valid()
  //@ reads Pool::used_
  //@ ensures result == Pool::used_
  static size_t used() { return used_; }

  CPLUSP_TRUSTED("the pool is one block made with new, and an index handed out stays inside it")
  //@ requires valid() && 0 < size && size <= 4096 - used()
  //@ modifies Pool::used_
  //@ ensures valid() && result == old(used()) && used() == old(used()) + size
  static size_t acquire(size_t size);

  CPLUSP_TRUSTED("release only moves the start of the free part back to the front of the pool")
  //@ modifies Pool::used_
  //@ ensures used() == 0 && valid()
  static void release();

 private:
  static size_t used_;
};

size_t Pool::used_ = 0;

//@ requires Pool::valid() && 0 < size && size <= 4096
//@ modifies Pool::used_
//@ ensures Pool::valid()
void blind_acquire(size_t size) {
  Pool::acquire(size);
}

// A twin with an argument takes its arguments before its globals, decision 0174.
class Scale {
 public:
  Scale() = delete;
  //@ requires -1000 <= x && x <= 1000
  //@ ensures result == 2 * x
  static int32_t twice(int32_t x) { return 2 * x; }
  //@ requires -1000 <= x && x <= 1000
  //@ reads Scale::level_
  //@ ensures result == (Scale::level_ > x)
  static bool above(int32_t x) { return level_ > x; }

  static int32_t level_;
};

int32_t Scale::level_ = 0;

//@ ensures result == Scale::twice(3)
int32_t seven_wrong() { return 7; }
