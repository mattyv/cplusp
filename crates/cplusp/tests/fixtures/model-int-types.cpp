#include <array>
#include <chrono>
#include <cstddef>
#include <cstdint>
#include "../../../../include/cplusp.h"

// Types that are an integer or a fixed sequence in the model, decision 0175. An enum class with a value written is its underlying
// integer, and an enumerator is its value. A free operator is a function with a readable name, and a call of it is a call.
enum class Flag : uint32_t { None = 0, Read = 1, Write = 2, Exec = 4 };

//@ ensures result == ((static_cast<uint32_t>(flags) & static_cast<uint32_t>(flag)) == static_cast<uint32_t>(flag))
bool has(Flag flags, Flag flag) {
  return (static_cast<uint32_t>(flags) & static_cast<uint32_t>(flag)) == static_cast<uint32_t>(flag);
}

//@ ensures static_cast<uint32_t>(result) == (static_cast<uint32_t>(a) | static_cast<uint32_t>(b))
Flag operator|(Flag a, Flag b) {
  return static_cast<Flag>(static_cast<uint32_t>(a) | static_cast<uint32_t>(b));
}

//@ ensures static_cast<uint32_t>(result) == (static_cast<uint32_t>(a) & static_cast<uint32_t>(b))
Flag operator&(Flag a, Flag b) {
  return static_cast<Flag>(static_cast<uint32_t>(a) & static_cast<uint32_t>(b));
}

// The laws of the bits: a flag that was set stays set, and the overlap keeps a flag both sides have.
//@ ensures (static_cast<uint32_t>(result) & static_cast<uint32_t>(flag)) == static_cast<uint32_t>(flag)
//@ ensures (static_cast<uint32_t>(flags) & 1) == 1 ==> (static_cast<uint32_t>(result) & 1) == 1
Flag grant(Flag flags, Flag flag) {
  return flags | flag;
}

//@ ensures result == (((static_cast<uint32_t>(a) & static_cast<uint32_t>(Flag::Write)) == static_cast<uint32_t>(Flag::Write)) && ((static_cast<uint32_t>(b) & static_cast<uint32_t>(Flag::Write)) == static_cast<uint32_t>(Flag::Write)))
bool both_may_write(Flag a, Flag b) {
  return has(a & b, Flag::Write);
}

//@ ensures result == true
bool reader_and_writer_cannot_exec() {
  Flag f = Flag::Read | Flag::Write;
  return has(f, Flag::Write) && !has(f, Flag::Exec);
}

// An enum class as an index, and a std::array by value and as a result with a brace return.
enum class Level : uint8_t { Low = 0, Medium = 1, High = 2 };

//@ requires static_cast<size_t>(level) < 3
//@ ensures result == table[static_cast<size_t>(level)]
int32_t lookup(const std::array<int32_t, 3>& table, Level level) {
  return table[static_cast<size_t>(level)];
}

//@ ensures result[0] == 10 && result[1] == 20 && result[2] == 30
std::array<int32_t, 3> default_table() {
  return {10, 20, 30};
}

//@ ensures result == 30
int32_t high_weight() {
  return lookup(default_table(), Level::High);
}

//@ requires code < 3
//@ ensures result == table[code]
int32_t lookup_code(const std::array<int32_t, 3>& table, uint8_t code) {
  return lookup(table, static_cast<Level>(code));
}

// A duration in milliseconds is its count, an int64.
//@ requires -0x8000000000000000 <= a.count() + b.count() <= 0x7FFFFFFFFFFFFFFF
//@ ensures result.count() == a.count() + b.count()
std::chrono::milliseconds add(std::chrono::milliseconds a, std::chrono::milliseconds b) {
  return a + b;
}

//@ ensures result.count() == 2500
std::chrono::milliseconds two_and_a_half() {
  return add(std::chrono::milliseconds{1000}, std::chrono::milliseconds{1500});
}

// A free operator on a struct.
struct Point {
  int32_t x;
  int32_t y;
};

//@ requires -0x40000000 <= a.x < 0x40000000 && -0x40000000 <= b.x < 0x40000000
//@ requires -0x40000000 <= a.y < 0x40000000 && -0x40000000 <= b.y < 0x40000000
//@ ensures result.x == a.x + b.x && result.y == a.y + b.y
Point operator+(Point a, Point b) {
  return Point{a.x + b.x, a.y + b.y};
}

//@ requires -0x40000000 <= p.x < 0x40000000 && -0x40000000 <= p.y < 0x40000000
//@ ensures result.x == p.x + 1 && result.y == p.y + 1
Point shifted(Point p) {
  return p + Point{1, 1};
}

// A const reference to a scalar is the scalar by value.
CPLUSP_TRUSTED("const_cast for a legacy function that only reads")
//@ ensures result == x
int32_t read_through(const int32_t& x);

//@ requires -0x40000000 <= x < 0x40000000
//@ ensures result == 2 * x
int32_t doubled(int32_t x) {
  int32_t a = read_through(x);
  int32_t b = read_through(x);
  return a + b;
}

// A std::array by value is a copy that only the function sees.
//@ requires -0x40000000 <= t[0] < 0x40000000 && -0x40000000 <= t[2] < 0x40000000
//@ ensures result == t[0] + t[2]
int32_t ends(std::array<int32_t, 3> t) {
  return t[0] + t[2];
}
