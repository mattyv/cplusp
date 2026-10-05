#include <cstdint>
#include <memory>
#include <vector>

struct Base {
  virtual int32_t value() const { return 1; }
  virtual ~Base() = default;
};

struct Derived : Base {
  std::vector<uint8_t> name = std::vector<uint8_t>(32, 0);
  int32_t value() const override { return 2; }
};

//@ ensures result == 2
int32_t value_of_new() {
  std::unique_ptr<Base> p = std::make_unique<Derived>();
  return p->value();
}
