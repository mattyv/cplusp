#include <cstdint>
class Counter {
public:
  int32_t value() const { return value_; }
  void add(int32_t n) { value_ += n; }

private:
  int32_t value_ = 0;
};
