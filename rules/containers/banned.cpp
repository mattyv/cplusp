#include <cstdint>
#include <vector>

int32_t first_then_grow(std::vector<int32_t>& v) {
  const int32_t& r = v[0];  // BANNED
  v.push_back(1);
  return r;
}

int32_t last(std::vector<int32_t>& v) {
  int32_t& b = v.back();  // BANNED
  return b;
}

#include <map>

std::size_t read_count(std::map<int32_t, int32_t>& m, int32_t k) {
  int32_t v = m[k];  // BANNED
  return m.size() + static_cast<std::size_t>(v);
}
