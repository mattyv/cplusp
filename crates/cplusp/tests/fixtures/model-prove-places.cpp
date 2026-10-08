#include <cstdint>
#include <vector>

// The start and the step of a for loop each keep their own line, decision 0069.
uint32_t back(uint32_t n) {
  uint32_t s = 0;
  //@ decreases n - i
  for (uint32_t i = n - 1;
       i < n;
       i = i + 2) {
    s = i;
  }
  return s;
}

// An obligation on an ensures line has the requires lines as assumptions.
//@ requires v[10] == 0
//@ ensures v[20] == 0
int32_t contract(const std::vector<int32_t>& v) {
  return 0;
}

// The loop must keep an invariant under all the invariants of its loop. At the start, it has only what holds before the loop.
//@ requires 0 <= n && n <= 10
int32_t keep(int32_t n) {
  int32_t j = 0;
  //@ invariant j <= 3
  //@ invariant 0 <= j
  //@ decreases n - j
  while (j < n) {
    ++j;
  }
  return j;
}

//@ requires 0 <= n
int32_t start(int32_t n) {
  int32_t j = 0;
  //@ invariant 1 <= j
  //@ invariant 0 <= j
  //@ decreases n - j
  while (j < n) {
    ++j;
  }
  return j;
}

// The condition of a loop, and its end, assume all the invariants of the loop.
size_t cond(const std::vector<int32_t>& v) {
  size_t i = 0;
  //@ invariant i <= 10
  //@ decreases 10 - i
  while (i < 10 && v[i] == 0) {
    ++i;
  }
  return i;
}
