#include <cstdint>
#include <memory>
#include <utility>

//@ requires p != nullptr
//@ requires -0x40000000 <= *p < 0x40000000
//@ ensures result == 2 * old(*p)
int32_t take(std::unique_ptr<int32_t> p) {
  std::unique_ptr<int32_t> q = std::move(p);
  return *q + *q;
}
