#include <cstdint>
#include <memory>

// A read of a unique_ptr that may be null does not prove, decision 0142.
//@ ensures true
std::unique_ptr<int32_t> maybe(int32_t x) {
  return std::make_unique<int32_t>(x);
}

int32_t read(int32_t x) {
  std::unique_ptr<int32_t> p = maybe(x);
  return *p;
}
