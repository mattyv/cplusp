#include <cstdint>

// A sum that stops at the ends of the range, and does not overflow. One operand is widened first, so the sum is an int64_t sum and cannot
// overflow, and then it is cut to the range. The contract names the three cases: above the range, below it, and inside it. Together
// they say what the result is for every pair, so the function has no precondition. clamp cuts a value to [lo, hi], and it is
// defined only when lo <= hi, which the contract requires. The standard std::clamp has the same limit and no contract for it.
//@ ensures a + b > 2147483647 ==> result == 2147483647
//@ ensures a + b < -2147483648 ==> result == -2147483648
//@ ensures -2147483648 <= a + b && a + b <= 2147483647 ==> result == a + b
int32_t saturating_add(int32_t a, int32_t b) {
  int64_t sum = int64_t{a} + b;
  if (sum > INT32_MAX) {
    return INT32_MAX;
  }
  if (sum < INT32_MIN) {
    return INT32_MIN;
  }
  return static_cast<int32_t>(sum);
}

//@ requires lo <= hi
//@ ensures lo <= result && result <= hi
//@ ensures x < lo ==> result == lo
//@ ensures x > hi ==> result == hi
//@ ensures lo <= x && x <= hi ==> result == x
int32_t clamp(int32_t x, int32_t lo, int32_t hi) {
  if (x < lo) {
    return lo;
  }
  if (x > hi) {
    return hi;
  }
  return x;
}

// A verified caller: the successor never goes down, and it is x + 1 below the top of the range.
//@ ensures result >= x && (x < 2147483647 ==> result == x + 1)
int32_t successor(int32_t x) {
  return saturating_add(x, 1);
}
