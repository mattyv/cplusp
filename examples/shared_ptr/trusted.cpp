#include <cstdint>
#include <memory>

// Trusted: two owners share one int, and the function returns the value. The refcount is hard to reason about, and the gate
// refuses std::shared_ptr under the shared_ptr row, which is the point. Verified code sees only the contract in example.cpp.
int32_t shared_value(int32_t x) {
  std::shared_ptr<int32_t> a = std::make_shared<int32_t>(x);
  std::shared_ptr<int32_t> b = a;
  return *b;
}
