#include <cstddef>
#include <cstdint>
#include <span>

// Forms of a span with no rule yet are refused at their lines, decision 0078.
size_t count(std::span<const uint8_t> key) {
  return key.size();
}

size_t two(std::span<const uint8_t> key) {
  size_t n = count(key.subspan(1, 2));
  return n;
}

size_t head(std::span<const uint8_t> key) {
  size_t n = count(key.first(2));
  return n;
}
