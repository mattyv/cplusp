#include <cstdint>
class Shape {
public:
  virtual ~Shape() = default;
  virtual int32_t sides() const = 0;
};

class Square : public Shape {
public:
  int32_t sides() const override { return 4; }
};

int32_t count_sides(const Shape& s) {
  return s.sides();
}
