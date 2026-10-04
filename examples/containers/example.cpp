#include <cstddef>
#include <cstdint>
#include <vector>

// A read from a vector by index. The contract carries the bound, and the caller proves it.
//@ requires i < v.size()
//@ ensures result == v[i]
int32_t element(const std::vector<int32_t>& v, size_t i) {
  return v.at(i);
}
