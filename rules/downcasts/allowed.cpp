class Shape {
public:
  virtual ~Shape() = default;
  virtual int sides() const = 0;
};

class Square : public Shape {
public:
  int sides() const override { return 4; }
};

int count_sides(const Shape& s) {
  return s.sides();
}
