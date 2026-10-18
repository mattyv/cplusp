#include <cstdint>

// Two ensures lines that fail on one return are two failures, though Dafny reports both at one place, decision 0155.
//@ ensures result >= 1
//@ ensures result <= 0
int32_t both(int32_t a) {
  return a;
}
