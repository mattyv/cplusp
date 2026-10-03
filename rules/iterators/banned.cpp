#include <cstdint>
#include <iterator>
#include <vector>

int64_t first_two(const std::vector<int64_t>& values) {
  auto it = values.begin();  // BANNED
  int64_t a = *it;
  ++it;
  int64_t b = *it;
  return a + b;
}

int64_t third(const std::vector<int64_t>& values) {
  return *std::next(values.begin(), 2);  // BANNED
}

bool has_negative(const std::vector<int64_t>& values) {
  for (std::vector<int64_t>::const_iterator it = values.begin(); it != values.end(); ++it) {  // BANNED
    if (*it < 0) {
      return true;
    }
  }
  return false;
}

int32_t grow_in_loop(std::vector<int32_t>& v) {
  int32_t s = 0;
  for (const int32_t x : v) {  // BANNED
    s += x;
    v.push_back(x);
  }
  return s;
}

void grow(std::vector<int32_t>& v, int32_t x);

int32_t grow_through_call(std::vector<int32_t>& v) {
  int32_t s = 0;
  for (const int32_t x : v) {  // BANNED
    s += x;
    grow(v, x);
  }
  return s;
}
