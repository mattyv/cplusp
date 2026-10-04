#include <cstdint>

// An operator is a pure function: a free function with by-value parameters, and no side effect. Its contract is the contract
// of any function, and the prover calls it as one. No assignment, increment or decrement operator is overloaded.
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
