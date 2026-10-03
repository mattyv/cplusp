#include <cstdint>
class Shape {
public:
  virtual ~Shape() = default;
  virtual int32_t sides() const = 0;
};

class Square : public Shape {
public:
  int32_t sides() const override { return 4; }
  int32_t edge() const { return 1; }
};

int32_t edge_of(const Shape& s) {
  return static_cast<const Square&>(s).edge();  // BANNED
}

int32_t edge_or_zero(const Shape* s) {
  return dynamic_cast<const Square*>(s) != nullptr ? dynamic_cast<const Square*>(s)->edge() : 0;  // BANNED
}
