#include <cstdint>
#include <map>

//@ ensures result == (m.contains(k) ? m.at(k) : 0)
//@ ensures m.size() == old(m.size())
int32_t value_or_zero(std::map<int32_t, int32_t>& m, int32_t k) {
  return m.contains(k) ? m.at(k) : 0;
}
