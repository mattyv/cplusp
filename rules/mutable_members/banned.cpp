#include <cstdint>
class Cache {
public:
  int32_t get() const {
    hits_ += 1;
    return value_;
  }

private:
  int32_t value_ = 0;
  mutable int32_t hits_ = 0;  // BANNED
};
