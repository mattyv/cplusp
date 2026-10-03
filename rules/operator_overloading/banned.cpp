#include <cstdint>
struct Vec2 {
  int32_t x = 0;
  int32_t y = 0;
  Vec2& operator+=(const Vec2& o) {  // BANNED
    x += o.x;
    y += o.y;
    return *this;
  }
  int32_t& operator[](int32_t i) { return i == 0 ? x : y; }  // BANNED
  Vec2 operator*(int32_t k) { return Vec2{x * k, y * k}; }  // BANNED
};

Vec2& operator<<(Vec2& v, int32_t k) {  // BANNED
  v.x = k;
  return v;
}
