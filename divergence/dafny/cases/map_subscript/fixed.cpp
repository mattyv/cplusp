#include <cstddef>
#include <cstdint>
#include <map>

//@ requires !m.contains(k)
//@ ensures result == m.size()
std::size_t count_after_read(std::map<int32_t, int32_t>& m, int32_t k) {
  int32_t v = m.contains(k) ? m.at(k) : 0;
  return m.size() + static_cast<std::size_t>(v);
}
