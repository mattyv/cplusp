#include <cstdint>

// Loops, writes to locals and an unsigned count, decision 0061. Each function proves.
//@ requires 0 <= n && n <= 1000
//@ ensures 2 * result == n * (n - 1)
int64_t triangle(int32_t n) {
  int64_t acc = 0;
  //@ invariant 0 <= i && i <= n
  //@ invariant 2 * acc == i * (i - 1)
  //@ decreases n - i
  for (int32_t i = 0; i < n; ++i) {
    acc = acc + i;
  }
  return acc;
}

//@ requires 0 <= n
//@ ensures result == 0
int32_t down(int32_t n) {
  int32_t k = n;
  //@ invariant 0 <= k
  //@ decreases k
  while (k > 0) {
    k--;
  }
  return k;
}

//@ ensures result == n
uint64_t count(uint64_t n) {
  uint64_t c = 0;
  //@ invariant c <= n
  //@ decreases n - c
  while (c < n) {
    c = c + 1;
  }
  return c;
}
