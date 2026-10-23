#include <array>
#include <chrono>
#include <cstddef>
#include <cstdint>

// An or that is an and, a grant that grants nothing, a table with a wrong element, a sum that drops a count, and an operator
// that adds one side twice, decision 0175.
enum class Flag : uint32_t { None = 0, Read = 1, Write = 2, Exec = 4 };

//@ ensures static_cast<uint32_t>(result) == (static_cast<uint32_t>(a) | static_cast<uint32_t>(b))
Flag operator|(Flag a, Flag b) {
  return static_cast<Flag>(static_cast<uint32_t>(a) & static_cast<uint32_t>(b));
}

//@ ensures (static_cast<uint32_t>(result) & static_cast<uint32_t>(flag)) == static_cast<uint32_t>(flag)
Flag grant(Flag flags, Flag flag) {
  return flags;
}

//@ ensures result[0] == 10 && result[1] == 20 && result[2] == 30
std::array<int32_t, 3> default_table() {
  return {10, 20, 31};
}

//@ requires 0 <= a.count() <= 1000 && 0 <= b.count() <= 1000
//@ ensures result.count() == a.count() + b.count()
std::chrono::milliseconds add(std::chrono::milliseconds a, std::chrono::milliseconds b) {
  return a;
}

struct Point {
  int32_t x;
  int32_t y;
};

//@ requires -0x40000000 <= a.x < 0x40000000 && -0x40000000 <= b.x < 0x40000000
//@ requires -0x40000000 <= a.y < 0x40000000 && -0x40000000 <= b.y < 0x40000000
//@ ensures result.x == a.x + b.x && result.y == a.y + b.y
Point operator+(Point a, Point b) {
  return Point{a.x + a.x, a.y + b.y};
}
