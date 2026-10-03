#include <cstdint>
#include <numeric>
#include <vector>

//@ ensures result == sum of v
int64_t total(const std::vector<int64_t>& v) {
  return std::accumulate(v.begin(), v.end(), 0);
}
