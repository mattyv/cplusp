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

#include <map>

bool has(const std::map<int32_t, int32_t>& m, int32_t k) {
  return m.contains(k);
}

int32_t get_or_zero(const std::map<int32_t, int32_t>& m, int32_t k) {
  return m.contains(k) ? m.at(k) : 0;
}

int32_t read(const int32_t* p);

int32_t first_by_copy(std::vector<int32_t>& v) {
  int32_t first = v[0];
  return read(&first);
}
