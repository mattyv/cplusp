#include <cstdint>

struct Base {
  virtual int32_t value() const { return 1; }
  virtual ~Base() = default;
};

struct Derived : Base {
  int32_t value() const override { return 2; }
};

//@ ensures result == b.value()
int32_t value_through_base(const Base& b) {
  return b.value();
}

//@ ensures result == d.value()
int32_t value_of(const Derived& d) {
  return value_through_base(d);
}
