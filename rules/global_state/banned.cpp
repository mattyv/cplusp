#include <cstdint>

int32_t total = 0;

struct Tally {
  static int32_t n;
};

int32_t Tally::n = 0;

//@ requires total < 0x7FFFFFFF
//@ modifies total
//@ ensures total == old(total) + 1
void bump() {
  total += 1;
}

// A write with no modifies line.
//@ requires total < 0x7FFFFFFF
//@ ensures total == old(total) + 1
void bump_unlisted() {
  total += 1;  // BANNED
}

// A read with no reads line.
bool positive() {
  return total > 0;  // BANNED
}

// A reads line where the body writes.
//@ reads total
void reset() {
  total = 0;  // BANNED
}

// The wrong name on the line.
//@ requires total < 0x7FFFFFFF
//@ modifies Tally::n
void bump_wrong() {
  total += 1;  // BANNED
}

// A call to a function whose line lists a global, with no line of its own.
//@ requires total < 0x7FFFFFFF
void through_a_call() {
  bump();  // BANNED
}
