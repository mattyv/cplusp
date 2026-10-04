#include <algorithm>
#include <cstdint>
#include <vector>

int64_t sum_by_reference(const std::vector<int64_t>& values) {
  int64_t total = 0;
  std::for_each(values.begin(), values.end(), [&total](int64_t v) { total += v; });  // BANNED
  return total;
}

int64_t stored_lambda(int64_t x) {
  auto twice = [](int64_t v) { return v * 2; };  // BANNED
  return twice(x);
}

struct Scaler {
  int64_t factor = 2;
  int64_t count(const std::vector<int64_t>& values) const {
    return std::count_if(values.begin(), values.end(), [this](int64_t v) { return v > factor; });  // BANNED
  }
};

int64_t counted(const std::vector<int64_t>& values, int64_t k) {
  return std::count_if(values.begin(), values.end(), [k, n = 0](int64_t v) mutable { return ++n > 1 && v > k; });  // BANNED also: plain_int
}
