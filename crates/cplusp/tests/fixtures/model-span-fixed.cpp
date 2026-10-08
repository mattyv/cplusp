#include <cstdint>
#include <span>

// A span with a fixed extent keeps its length, decision 0070.
//@ ensures result == 3
uint64_t size(std::span<const int32_t, 3> v) {
  return v.size();
}

//@ ensures result == v[0]
int32_t head(std::span<const int32_t, 3> v) {
  return v[0];
}
