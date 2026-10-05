#include <cstdint>
#include "../../include/cplusp.h"

// std::launder is trusted, and its contract is the plain read it stands for. The body is in trusted.cpp. The caller reads twice,
// and the contract says each read is the object, so the object does not change between them.
CPLUSP_TRUSTED("std::launder, and the contract is the plain read")
//@ requires p != nullptr
//@ ensures result == *p
int32_t read_back(const int32_t* p);

//@ requires p != nullptr
//@ requires -0x40000000 <= *p < 0x40000000
//@ ensures result == 2 * *p
int32_t read_twice(const int32_t* p) {
  int32_t a = read_back(p);
  int32_t b = read_back(p);
  return a + b;
}
