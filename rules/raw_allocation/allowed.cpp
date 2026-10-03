#include <memory>

int make_and_read() {
  std::unique_ptr<int> p = std::make_unique<int>(1);
  return *p;
}
