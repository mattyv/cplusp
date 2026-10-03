#include <algorithm>
#include <cstdint>
#include <vector>

// Passed straight to a std:: call, capturing by value.
int64_t count_above(const std::vector<int64_t>& values, int64_t limit) {
  return std::count_if(values.begin(), values.end(), [limit](int64_t v) { return v > limit; });
}
