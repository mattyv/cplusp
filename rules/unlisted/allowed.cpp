#include <cstddef>
#include <cstdint>
#include <optional>
#include <vector>

// Ordinary code: every kind of node here is on the lists of the row.
struct Point {
  int32_t x = 0;
  int32_t y = 0;
};

//@ requires -0x40000000 <= p.x < 0x40000000 && -0x40000000 <= p.y < 0x40000000
//@ ensures result == p.x + p.y
int32_t sum(const Point& p) {
  return p.x + p.y;
}

//@ ensures result.has_value() == (v.size() > 0)
std::optional<int32_t> first(const std::vector<int32_t>& v) {
  if (v.empty()) {
    return std::nullopt;
  }
  return v[0];
}

//@ ensures result <= v.size()
std::size_t count_positive(const std::vector<int32_t>& v) {
  std::size_t n = 0;
  for (const int32_t x : v) {
    if (x > 0) {
      ++n;
    }
  }
  return n;
}

// The kinds added to the lists by hand, each with its sample: a namespace, two aliases, a static_assert, a default
// argument, value initialisation, a do loop, a continue, and a structured binding.
namespace shapes {

using Count = std::size_t;
typedef int32_t Coord;
static_assert(sizeof(Coord) == 4);

struct Raw {
  Coord a = 0;
  Coord b = 0;
};

//@ requires -0x40000000 <= a < 0x40000000 && -0x40000000 <= b < 0x40000000
//@ ensures result == a + b
Coord add(Coord a, Coord b = 0) {
  return a + b;
}

//@ requires -0x40000000 <= x < 0x40000000
//@ ensures result == x
Coord with_default(Coord x) {
  return add(x);
}

//@ ensures result == 0
Coord zero() {
  return Coord();
}

//@ ensures result == 0
int32_t tail() {
  int32_t cells[3] = {1};
  return cells[2];
}

//@ requires n > 0
//@ ensures result == n
Count countdown(Count n) {
  Count steps = 0;
  do {
    ++steps;
  } while (steps < n);
  return steps;
}

//@ ensures result <= v.size()
Count non_positive(const std::vector<int32_t>& v) {
  Count n = 0;
  for (const int32_t x : v) {
    if (x > 0) {
      continue;
    }
    ++n;
  }
  return n;
}

//@ ensures result.a == x && result.b == x
Raw pair_of(Coord x) {
  return Raw{x, x};
}

//@ ensures result == 2 * x
Coord both(Coord x) {
  auto [a, b] = pair_of(x);
  return a + b;
}

}  // namespace shapes
