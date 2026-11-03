#include <cstdint>
int32_t repeated(int32_t x) {
  x = (int32_t)x;
  x = (int32_t)x;
  x = (int32_t)x;
  x = (int32_t)x;
  x = (int32_t)x;
  return x;
}
int32_t distinct_messages(int32_t x) {
  try {
    if (x < 0) throw x;
    if (x == 0) throw x;
    return x;
  } catch (int32_t) {
    return 0;
  }
}
