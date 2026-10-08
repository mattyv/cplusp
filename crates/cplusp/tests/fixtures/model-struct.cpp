#include <cstdint>

// Structs of scalars are Dafny datatypes, decision 0073.
struct Point {
  int32_t x;
  int32_t y;
};

struct Span2 {
  Point lo;
  Point hi;
};

//@ requires -1000 <= p.x && p.x <= 1000 && -1000 <= p.y && p.y <= 1000
//@ ensures result == p.x + p.y
int32_t sum(Point p) {
  return p.x + p.y;
}

//@ ensures result.x == p.y && result.y == p.x
Point swap(const Point& p) {
  return Point{p.y, p.x};
}

//@ requires -1000 <= p.x && p.x <= 1000
//@ ensures result.x == p.x + 1 && result.y == p.y
Point right(Point p) {
  Point q = {p.x + 1, p.y};
  return q;
}

//@ requires -1000 <= p.x && p.x <= 1000 && -1000 <= p.y && p.y <= 1000
//@ ensures result == p.x + p.y
int32_t calls_sum(Point p) {
  return sum(p);
}

//@ requires 0 <= b.lo.x && b.lo.x <= b.hi.x && b.hi.x <= 1000
//@ ensures result == b.hi.x - b.lo.x
int32_t width(const Span2& b) {
  return b.hi.x - b.lo.x;
}
