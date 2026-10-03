#include <cstdint>
int32_t positive_or_one(int32_t x) {
  return x > 0 ? x : 1;
}

int32_t above_hundred(int32_t x) {
  return x > 100 ? x - 100 : 0;
}
