#include <cstdint>

struct Base {
  virtual int32_t value() const { return 1; }
  virtual ~Base() = default;
};

struct Derived : Base {
  int32_t value() const override { return 2; }
};

int32_t by_reference(const Derived& d) {
  const Base& b = d;
  return b.value();
}

int32_t passed(const Base& b) {
  return b.value();
}

int32_t call_by_reference(const Derived& d) {
  return passed(d);
}
