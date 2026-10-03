#include <cstdint>

struct Point {
  int32_t x;
  int32_t y;
};

//@ requires p.x <= 0x7FFFFFFA
//@ ensures result == p.x + 5
int32_t keep(Point p) {
  Point q = p;
  q.x = 5;
  return p.x + q.x;
}
