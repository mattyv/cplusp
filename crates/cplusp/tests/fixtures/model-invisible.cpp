#include <cstdint>

// A character that the eye cannot see is named by its code point, decision 0125. A tab is white space.
//@ requires x < 1
//@ ensures	result == x
int32_t nb(int32_t x) {
  return x;
}
