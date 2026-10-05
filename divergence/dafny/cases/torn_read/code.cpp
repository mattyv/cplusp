#include <cstdint>

int32_t shared = 0;

// A trusted getter. Another thread writes `shared`.
//@ reads shared
//@ ensures result == shared
int32_t read_shared() {
  return shared;
}

//@ reads shared
//@ ensures result == 0
int32_t difference() {
  return read_shared() - read_shared();
}
