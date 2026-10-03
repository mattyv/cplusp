// The edge where the naive model and the C++ part ways: q is a copy, so changing q.x leaves p.x as it was.
#include <cstdint>
#include <cstdio>

struct Point {
  int32_t x;
  int32_t y;
};

int32_t keep(Point p);

int main() {
  std::printf("%d\n", keep(Point{1, 2}));
  return 0;
}
