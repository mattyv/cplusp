#include <cstdint>
#include "../../../../include/cplusp.h"

// The contract lines in a trusted body belong to it and are not read, and a marked declaration names the trusted function,
// decision 0103.
CPLUSP_TRUSTED("counts with a loop")
//@ requires n >= 0 && n <= 1000
//@ ensures result == n
int32_t count(int32_t n);

int32_t count(int32_t n) {
  int32_t i = 0;
  //@ invariant i <= n
  while (i < n) {
    //@ assert i < n
    i = i + 1;
  }
  return i;
}

//@ requires n >= 0 && n <= 1000
//@ ensures result == n + 1
int32_t one_more(int32_t n) {
  int32_t c = count(n);
  return c + 1;
}
