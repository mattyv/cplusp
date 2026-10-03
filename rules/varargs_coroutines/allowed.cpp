#include <cstdint>
#include <span>

int64_t total(std::span<const int64_t> values) {
  int64_t t = 0;
  for (const int64_t v : values) {
    t += v;
  }
  return t;
}
