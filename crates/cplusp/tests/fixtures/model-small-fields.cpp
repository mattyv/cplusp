#include <cstdint>

// int8_t, int16_t and uint16_t can be fields of a plain struct, decision 0138.
struct Sample {
  int8_t delta;
  int16_t level;
  uint16_t count;
};

//@ requires -100 <= d <= 100
//@ ensures result.delta == d && result.level == 2 * d && result.count == 7
Sample make(int8_t d) {
  return Sample{d, static_cast<int16_t>(2 * d), 7};
}

//@ ensures result == s.level + s.count
int32_t total(Sample s) {
  return s.level + s.count;
}
