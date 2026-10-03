#include <cstdint>

struct Base {
  virtual int32_t value() const { return 1; }
  virtual ~Base() = default;
};

struct Derived : Base {
  int32_t value() const override { return 2; }
};

int32_t by_value(const Derived& d) {
  Base b = d;  // BANNED
  return b.value();
}

int32_t passed(Base b) {
  return b.value();
}

int32_t call_by_value(const Derived& d) {
  return passed(d);  // BANNED
}
