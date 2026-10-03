struct Vec2 {
  int x = 0;
  int y = 0;
  Vec2& operator=(const Vec2&) = default;
  Vec2 operator+(const Vec2& o) const { return Vec2{x + o.x, y + o.y}; }
  bool operator==(const Vec2& o) const { return x == o.x && y == o.y; }
};

Vec2 operator-(const Vec2& a, const Vec2& b) { return Vec2{a.x - b.x, a.y - b.y}; }
