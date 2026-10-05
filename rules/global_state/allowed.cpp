#include <cstdint>

int32_t total = 0;
const int32_t limit = 100;

struct Tally {
  static int32_t n;
};

int32_t Tally::n = 0;

// A write is on the modifies line.
//@ requires total < limit
//@ modifies total
//@ ensures total == old(total) + 1
void bump() {
  total += 1;
}

// A read is on the reads line. The constant needs no line.
//@ reads total
//@ ensures result == (total < limit)
bool below() {
  return total < limit;
}

// A static data member by its qualified name.
//@ requires Tally::n < 0x7FFFFFFF
//@ modifies Tally::n
//@ ensures Tally::n == old(Tally::n) + 1
void count() {
  Tally::n += 1;
}

// A caller lists what its callee changes.
//@ requires total < limit - 1
//@ modifies total
//@ ensures total == old(total) + 2
void twice() {
  bump();
  bump();
}

// Members are implicit, decision 0028. No line names them.
struct Counter {
  int32_t n = 0;
  //@ requires n < 0x7FFFFFFF
  //@ ensures n == old(n) + 1
  void step() {
    ++n;
  }
};
