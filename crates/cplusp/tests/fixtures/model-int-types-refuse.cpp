#include <array>
#include <chrono>
#include <cstdint>
// A cast in a contract that can change the value, a duration that is not milliseconds, and an operator that is a member,
// decision 0175.
enum class Flag : uint32_t { None = 0, Read = 1, Write = 2 };

//@ ensures result == static_cast<uint8_t>(flag)
uint8_t low_byte(Flag flag) {
  return static_cast<uint8_t>(flag);
}

//@ ensures result.count() == a.count()
std::chrono::seconds same(std::chrono::seconds a) {
  return a;
}

struct Point {
  int32_t x;
  int32_t y;

  //@ requires -0x40000000 <= x < 0x40000000 && -0x40000000 <= b.x < 0x40000000
  //@ ensures result.x == x + b.x
  Point operator+(Point b) const {
    return Point{x + b.x, y};
  }
};

// A braced list with fewer values than the std::array.
std::array<int32_t, 3> short_table() {
  return {10, 20};
}
