#include <cstdint>

struct Base {
  virtual int32_t value() const { return 1; }
  virtual ~Base() = default;
};

struct Derived : Base {
  int32_t value() const override { return 2; }
};

//@ ensures result == d.value()
int32_t value_of(const Derived& d) {
  Base b = d;
  return b.value();
}
