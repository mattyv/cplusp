#include <cstdint>
#include <memory>

// Trusted: the function allocates with new, and a unique_ptr takes the object at once, so nothing leaks. The gate refuses the
// new under the raw_allocation row, which is the point. Verified code sees only the contract in example.cpp.
std::unique_ptr<int32_t> make_box(int32_t x) {
  return std::unique_ptr<int32_t>(new int32_t(x));
}
