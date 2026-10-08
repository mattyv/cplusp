#include <cstdint>

// A companion file with words that it may not hold, decision 0079.
//@ ensures result == Max(a, b)
int32_t larger(int32_t a, int32_t b) {
  if (a < b) {
    return b;
  }
  return a;
}
