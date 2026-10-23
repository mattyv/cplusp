#include <cstddef>
#include <cstdint>
#include "../../../../include/cplusp.h"

// A static member function is a free function with the name of its class, decision 0174. Its globals are implicit parameters,
// decision 0173. A static that only reads, with a body of one return, gets a function twin that a contract can call, bare inside
// the class and qualified outside it.
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

  //@ requires valid() && count() < 1000
  //@ modifies Tally::count_
  //@ ensures valid() && count() == old(count()) + 1
  static void bump() { count_ += 1; }

  //@ modifies Tally::count_
  //@ ensures valid() && count() == 0
  static void reset() { count_ = 0; }

 private:
  static int32_t count_;
};

int32_t Tally::count_ = 0;

//@ requires Tally::valid() && Tally::count() <= 997
//@ modifies Tally::count_
//@ ensures Tally::valid() && Tally::count() == old(Tally::count()) + 3 && result == Tally::count()
int32_t three_bumps() {
  Tally::bump();
  Tally::bump();
  Tally::bump();
  return Tally::count();
}

//@ modifies Tally::count_
//@ ensures result == 3
int32_t reset_then_three() {
  Tally::reset();
  return three_bumps();
}

// A second class with a valid() of its own, and a trusted static, as in examples/arena.
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

 private:
  static size_t used_;
};

size_t Pool::used_ = 0;

//@ requires Pool::valid() && 0 < n && 0 < m && n + m <= 4096 - Pool::used()
//@ modifies Pool::used_
//@ ensures Pool::valid() && result == old(Pool::used()) + n && Pool::used() == old(Pool::used()) + n + m
size_t second_block(size_t n, size_t m) {
  Pool::acquire(n);
  return Pool::acquire(m);
}

// A struct with a field, a const member and a static member side by side.
struct Counter {
  int32_t n_;

  //@ ensures result == n_
  int32_t value() const { return n_; }

  //@ reads Counter::made
  //@ ensures result == Counter::made
  static int32_t made_count() { return made; }

  static int32_t made;
};

int32_t Counter::made = 0;

//@ requires c.n_ == 2 && Counter::made == 5
//@ reads Counter::made
//@ ensures result == 7
int32_t seven(const Counter& c) {
  return c.value() + Counter::made_count();
}
