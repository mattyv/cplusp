#include <cstdint>

// The count lives in a static data member, which has a name a caller's contract can list.
struct Tally {
  static int32_t n;
};

int32_t Tally::n = 0;

//@ requires Tally::n < 0x7FFFFFFF
//@ modifies Tally::n
//@ ensures Tally::n == old(Tally::n) + 1 && result == Tally::n
int32_t counter() {
  Tally::n += 1;
  return Tally::n;
}
