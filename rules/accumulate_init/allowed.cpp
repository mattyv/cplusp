#include <cstdint>
#include <numeric>
#include <vector>

int64_t total(const std::vector<int64_t>& v) {
  return std::accumulate(v.begin(), v.end(), int64_t{0});
}

int32_t total32(const std::vector<int32_t>& v) {
  return std::accumulate(v.begin(), v.end(), int32_t{0});
}
