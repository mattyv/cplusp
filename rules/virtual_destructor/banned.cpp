#include <cstdint>

struct Shape {  // BANNED
  virtual int32_t area() const { return 0; }
};

struct Named {  // BANNED
  virtual int32_t id() const = 0;
  ~Named() = default;
};
