#include <cstddef>
#include <cstdint>
#include <span>
#include <vector>

// subspan and empty, decision 0078.
//@ decreases key.size()
//@ ensures result == key.size()
size_t length(std::span<const uint8_t> key) {
  if (key.empty()) {
    return 0;
  }
  size_t rest = length(key.subspan(1));
  return rest + 1;
}

//@ ensures result == v.empty()
bool none(const std::vector<int32_t>& v) {
  return v.empty();
}

//@ requires !key.empty()
//@ ensures result == key.size() - 1
size_t tail(std::span<const uint8_t> key) {
  size_t n = length(key.subspan(1));
  return n;
}

//@ ensures result == key.size()
size_t fixed(std::span<const uint8_t, 4> key) {
  size_t n = length(key.subspan(0));
  return n;
}
