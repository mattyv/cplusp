#include <cstdint>
#include <memory>
#include <utility>

// A write through a unique_ptr, a move of one, and a unique_ptr with no const by reference have no rule yet, decision 0142.
int32_t write(int32_t x) {
  std::unique_ptr<int32_t> p = std::make_unique<int32_t>(x);
  *p = 1;
  return *p;
}

std::unique_ptr<int32_t> pass(std::unique_ptr<int32_t> p) {
  return std::move(p);
}

//@ modifies p
void reset(std::unique_ptr<int32_t>& p) {
}

// Two unique_ptrs do not compare, as two pointers do not, decision 0142.
bool same(const std::unique_ptr<int32_t>& p, const std::unique_ptr<int32_t>& q) {
  return p == q;
}
