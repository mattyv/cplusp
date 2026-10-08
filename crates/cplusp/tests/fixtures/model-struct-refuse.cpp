#include <cstdint>

// Structs with no rule are refused at their lines, decision 0073.
struct Handle {
  int32_t* p;
};

int32_t through(Handle h) {
  return 0;
}

struct Point {
  int32_t x;
  int32_t y;
};

int32_t write_field(Point p) {
  p.x = 1;
  return p.x;
}

//@ ensures result == p.z
int32_t no_field(Point p) {
  return p.x;
}

int32_t partial(int32_t a) {
  Point q = {a};
  return q.x;
}
