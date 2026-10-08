#include <cstddef>
#include <cstdint>
#include <span>

// An offset past the end is named at its line, decision 0078.
//@ decreases key.size()
//@ ensures result == key.size()
size_t length(std::span<const uint8_t> key) {
  if (key.empty()) {
    return 0;
  }
  size_t rest = length(key.subspan(1));
  return rest + 1;
}

size_t skip(std::span<const uint8_t> key) {
  size_t n = length(key.subspan(5));
  return n;
}
