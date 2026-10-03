#include <cstdint>
#include <memory>
#include <vector>

int32_t make_and_read() {
  std::shared_ptr<int32_t> p;  // BANNED
  p = std::make_shared<int32_t>(1);  // BANNED
  return *p;
}

int32_t by_reference(const std::shared_ptr<int32_t>& p) {  // BANNED
  return *p;
}

int32_t by_pointer(const std::shared_ptr<int32_t>* p) {  // BANNED
  return **p;
}

int32_t in_container(const std::vector<std::shared_ptr<int32_t>>& items) {  // BANNED
  return items.empty() ? 0 : 1;
}
