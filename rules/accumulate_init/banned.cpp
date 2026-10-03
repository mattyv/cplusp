#include <cstdint>
#include <numeric>
#include <vector>

int64_t total(const std::vector<int64_t>& v) {
  return std::accumulate(v.begin(), v.end(), 0);  // BANNED
}
