#include <cstdint>
class Meters {
public:
  Meters(int32_t v) : value_(v) {}  // BANNED
  operator int32_t() const { return value_; }  // BANNED

private:
  int32_t value_;
};

int32_t twice(const Meters& m) {
  return m * 2;
}
