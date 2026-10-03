#include <cstdint>
#include <span>

int64_t sum(std::span<const int64_t> values) {
  int64_t total = 0;
  for (const int64_t v : values) {
    total += v;
  }
  return total;
}
