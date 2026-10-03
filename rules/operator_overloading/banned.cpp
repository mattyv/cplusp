struct Vec2 {
  int x = 0;
  int y = 0;
  Vec2& operator+=(const Vec2& o) {  // BANNED
    x += o.x;
    y += o.y;
    return *this;
  }
  int& operator[](int i) { return i == 0 ? x : y; }  // BANNED
  Vec2 operator*(int k) { return Vec2{x * k, y * k}; }  // BANNED
};

Vec2& operator<<(Vec2& v, int k) {  // BANNED
  v.x = k;
  return v;
}
