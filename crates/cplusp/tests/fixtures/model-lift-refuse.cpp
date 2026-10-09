#include <cstdint>

// A call that C++ may not evaluate once is refused at its line, decision 0104.
int32_t inc(int32_t x) {
  return x + 1;
}

bool both(int32_t x) {
  return x > 0 && inc(x) > 1;
}

int32_t pick(int32_t x) {
  return x > 0 ? inc(x) : 0;
}

int32_t loop(int32_t x) {
  int32_t i = 0;
  while (inc(i) < x) {
    i = i + 1;
  }
  return i;
}

bool either(int32_t x) {
  return x <= 0 || inc(x) > 1;
}

int32_t count_up(int32_t x) {
  int32_t s = 0;
  for (int32_t i = 0; inc(i) < x; i = i + 1) {
    s = s + 1;
  }
  return s;
}
