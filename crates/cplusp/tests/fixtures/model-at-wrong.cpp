#include <cstddef>
#include <cstdint>
#include <vector>

// An index that may be out of range does not prove, decision 0139. In C++ `at` would throw.
int32_t element(const std::vector<int32_t>& v, size_t i) {
  return v.at(i);
}
