#include <cstddef>
#include <cstdint>
#include <vector>

//@ ensures result == v.size()
size_t count(const std::vector<int32_t>& v) {
  return v.size();
}
