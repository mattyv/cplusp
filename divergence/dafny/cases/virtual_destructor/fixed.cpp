#include <cstdint>
#include <memory>
#include <string>

struct Base {
  virtual int32_t value() const { return 1; }
  virtual ~Base() = default;
};

struct Derived : Base {
  std::string name = "0123456789abcdef0123456789abcdef";
  int32_t value() const override { return 2; }
};

//@ ensures result == 2
int32_t value_of_new() {
  std::unique_ptr<Base> p = std::make_unique<Derived>();
  return p->value();
}
