#include <algorithm>
#include <cstdint>
#include <vector>

// Another algorithm, an init capture, a body of two statements, another range and a wide parameter have no rule, 0149 and 0157.
bool all_positive(const std::vector<int32_t>& v) {
  return std::all_of(v.begin(), v.end(), [](int32_t x) { return x > 0; });
}

int64_t above_next(const std::vector<int32_t>& v, int32_t k) {
  return std::count_if(v.begin(), v.end(), [m = k](int32_t x) { return x > m; });
}

int64_t two_steps(const std::vector<int32_t>& v) {
  return std::count_if(v.begin(), v.end(), [](int32_t x) {
    int32_t y = x;
    return y > 0;
  });
}

int64_t other_range(const std::vector<int32_t>& v) {
  return std::count_if(v.end(), v.end(), [](int32_t x) { return x > 0; });
}

int64_t wide_param(const std::vector<int32_t>& v) {
  return std::count_if(v.begin(), v.end(), [](int64_t x) { return x > 0; });
}
