#include <cstdint>

// A team policy that bans a variable index reaches prove through --policy, decision 0069.
//@ requires 0 <= i && i < 4
int32_t pick(int32_t i) {
  const int32_t a[4] = {1, 2, 3, 4};
  return a[i];
}
