// The edge where the naive model and the C++ part ways: the copy is a Base, so `b.value()` is Base's.
// The classes are the same text as in code.cpp, so the definitions agree.
#include <cstdint>
#include <cstdio>

struct Base {
  virtual int32_t value() const { return 1; }
  virtual ~Base() = default;
};

struct Derived : Base {
  int32_t value() const override { return 2; }
};

int32_t value_of(const Derived& d);

int main() {
  Derived d;
  std::printf("%d\n", value_of(d));
  return 0;
}
