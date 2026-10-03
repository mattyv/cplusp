#include <cstddef>
#include <cstdint>
#include <map>

//@ ensures result == m.size()
std::size_t count_after_read(std::map<int32_t, int32_t>& m, int32_t k) {
  int32_t v = m[k];
  return m.size() + static_cast<std::size_t>(v);
}
