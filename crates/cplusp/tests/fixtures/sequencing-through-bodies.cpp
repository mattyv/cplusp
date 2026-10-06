#include <cstdint>

int32_t total = 0;

int32_t a_write() {
  total += 1;
  return total;
}

int32_t b_write() {
  total += 2;
  return total;
}

int32_t add(int32_t a, int32_t b) {
  return a + b;
}

// Two callees that write a global in their bodies, with no line to say so. Two changes, whatever the state row says.
int32_t both() {
  return add(a_write(), b_write());
}
