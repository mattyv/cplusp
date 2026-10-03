#include <cstdint>
#include <memory>

int32_t make_and_read() {
  std::unique_ptr<int32_t> p = std::make_unique<int32_t>(1);
  return *p;
}
