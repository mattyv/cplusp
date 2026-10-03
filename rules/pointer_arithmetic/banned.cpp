#include <cstdint>

int64_t sum(const int64_t* values, int count) {
  int64_t total = 0;
  for (int i = 0; i < count; ++i) {
    total += *(values + i);  // BANNED
  }
  return total;
}
