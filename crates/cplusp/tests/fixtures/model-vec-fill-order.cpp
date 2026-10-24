#include <cstddef>
#include <cstdint>
#include <vector>

// The count and the value of `v(n, x)` are two arguments of one call. C++ does not fix their order, decision 0185.
int32_t fill_order() {
  int32_t k = 1;
  std::vector<int32_t> v(static_cast<size_t>(k), k++);
  return v[0];
}
