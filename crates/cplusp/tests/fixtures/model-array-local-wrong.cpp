#include <array>
#include <cstdint>

// The values of a local array keep their order, so a claim about another element fails, decision 0184.
//@ ensures result == 8
int32_t middle() {
  const std::array<int32_t, 3> t = {8, 9, 10};
  return t[1];
}

// A write changes one element, and the others stay.
//@ ensures result == 3
int32_t written() {
  std::array<int32_t, 2> t = {1, 2};
  t[0] = 3;
  return t[1];
}

int32_t g = 0;

//@ modifies g
//@ requires g < 100
//@ ensures g == old(g) + 1 && result == g
int32_t bump() {
  g = g + 1;
  return g;
}

// The values run first to last, so the second call gives the second value.
//@ modifies g
//@ requires g == 0
//@ ensures result == 1
int32_t second() {
  const std::array<int32_t, 2> t = {bump(), bump()};
  return t[1];
}

// A write past the end is out of range.
//@ ensures true
int32_t past_end() {
  std::array<int32_t, 2> t = {1, 2};
  t[2] = 3;
  return 0;
}
