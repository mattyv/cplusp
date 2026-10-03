#include <cstdint>

union Word {  // BANNED
  int32_t i;
  float f;
};

int32_t bits(Word w) {
  return w.i;  // BANNED
}
