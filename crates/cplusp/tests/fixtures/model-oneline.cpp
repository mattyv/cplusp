#include <cstdint>

// A loop on the line of its function's name does not take the function's contract lines, decision 0062.
//@ requires 0 <= n
//@ ensures result == 0
int32_t w4(int32_t n) { for (int32_t i = 0; i < n; ++i) { } return 0; }
