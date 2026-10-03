#include <cstddef>
#include <cstdint>
#include <vector>

//@ ensures result == v.size() - 1
std::size_t last_index(const std::vector<int32_t>& v) {
  return v.size() - 1;
}
