#include <cstdint>

// A static data member has a name a caller's contract can list.
struct Tally {
  static int32_t count;
};

int32_t Tally::count = 0;

//@ requires Tally::count < 0x7FFFFFFF
//@ modifies Tally::count
//@ ensures Tally::count == old(Tally::count) + 1 && result == Tally::count
int32_t bump() {
  Tally::count += 1;
  return Tally::count;
}
