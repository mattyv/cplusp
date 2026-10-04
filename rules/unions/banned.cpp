#include <cstdint>

union Word {  // BANNED
  int32_t i;
  double f;
};

int32_t bits(Word w) {
  return w.i;  // BANNED
}
