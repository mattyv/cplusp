class Shape {
public:
  virtual ~Shape() = default;
  virtual int sides() const = 0;
};

class Square : public Shape {
public:
  int sides() const override { return 4; }
  int edge() const { return 1; }
};

int edge_of(const Shape& s) {
  return static_cast<const Square&>(s).edge();  // BANNED
}

int edge_or_zero(const Shape* s) {
  const Square* sq = dynamic_cast<const Square*>(s);  // BANNED
  return sq != nullptr ? sq->edge() : 0;
}
