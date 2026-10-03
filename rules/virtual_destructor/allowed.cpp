#include <cstdint>

struct Shape {
  virtual int32_t area() const { return 0; }
  virtual ~Shape() = default;
};

struct Point {
  int32_t x = 0;
  int32_t y = 0;
};

class Mixin {
 public:
  virtual int32_t id() const = 0;

 protected:
  ~Mixin() = default;
};
