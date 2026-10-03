#include <memory>
#include <vector>

int make_and_read() {
  std::shared_ptr<int> p;  // BANNED
  p = std::make_shared<int>(1);  // BANNED
  return *p;
}

int by_reference(const std::shared_ptr<int>& p) {  // BANNED
  return *p;
}

int by_pointer(const std::shared_ptr<int>* p) {  // BANNED
  return **p;
}

int in_container(const std::vector<std::shared_ptr<int>>& items) {  // BANNED
  return items.empty() ? 0 : 1;
}
