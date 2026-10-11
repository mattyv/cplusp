#include <cstdint>

// A Hangul filler is a letter that the eye cannot see, so it is named by its code point, decision 0126.
//@ requires x <ㅤ 1
int32_t hf(int32_t x) {
  return x;
}
