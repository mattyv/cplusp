#include <cstddef>
#include <cstdint>
#include <vector>

// A slice in a contract that may start past the end is named at its line, decision 0085.
//@ ensures v[i..].size() == v.size() - i
bool part(const std::vector<int32_t>& v, size_t i) {
  return true;
}
