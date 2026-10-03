#include <cstdint>
class Meters {
public:
  explicit Meters(int32_t v) : value_(v) {}
  explicit operator int32_t() const { return value_; }

private:
  int32_t value_;
};

int32_t twice(const Meters& m) {
  return static_cast<int32_t>(m) * 2;
}
