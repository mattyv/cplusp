#include <cstdint>
#include <vector>

int32_t first_then_grow(std::vector<int32_t>& v) {
  int32_t r = v[0];
  v.push_back(1);
  return r;
}

int32_t total(const std::vector<int32_t>& v) {
  const std::vector<int32_t>& w = v;
  int32_t t = 0;
  for (const int32_t& x : w) {
    t += x;
  }
  return t;
}
