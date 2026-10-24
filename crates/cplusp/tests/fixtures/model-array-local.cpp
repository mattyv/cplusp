#include <array>
#include <cstddef>
#include <cstdint>
#include <span>

// A local std::array from a brace list of its length is the sequence of the values, decision 0184.
//@ ensures result == (s.size() >= 1 && s[0] == 7)
bool first_is_seven(std::span<const int32_t> s) {
  return s.size() >= 1 && s[0] == 7;
}

//@ ensures result == 9
int32_t middle() {
  const std::array<int32_t, 3> t = {8, 9, 10};
  return t[1];
}

//@ ensures result
bool passed() {
  const std::array<int32_t, 2> t = {7, 1};
  return first_is_seven(t);
}

//@ ensures result == 4
size_t length() {
  const std::array<uint8_t, 4> t = {0x47, 0x45, 0x54, 0x20};
  return t.size();
}

//@ ensures result == 3
int32_t written() {
  std::array<int32_t, 2> t = {1, 2};
  t[0] = 3;
  return t[0];
}

//@ requires -100 < x && x < 100
//@ ensures result == x + 1
int32_t from_values(int32_t x) {
  const std::array<int32_t, 2> t = {x, x + 1};
  return t[1];
}
