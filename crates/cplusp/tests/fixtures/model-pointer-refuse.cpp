#include <cstdint>

// A pointer with no const, and a test of a pointer as a bool, have no rule yet, decision 0140.
//@ modifies p
int32_t write(int32_t* p) {
  return 0;
}

int32_t test(const int32_t* p) {
  if (p) {
    return 1;
  }
  return 0;
}
