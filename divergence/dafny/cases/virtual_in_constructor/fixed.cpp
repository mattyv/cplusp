#include <cstdint>

struct Base {
  int32_t seen = 0;
  virtual int32_t kind() const { return 1; }
  virtual ~Base() = default;
};

struct Derived : Base {
  int32_t kind() const override { return 2; }
};

//@ ensures result == 2
int32_t seen_kind() {
  Derived d;
  d.seen = d.kind();
  return d.seen;
}
