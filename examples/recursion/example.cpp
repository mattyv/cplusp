#include <cstddef>
#include <cstdint>
#include <vector>

// A recursion needs a decreases clause, the measure that gets smaller at each call, and the prover proves it. It also needs a bound
// on the depth, since the stack is finite. The bound on v.size() is that bound, an assumption about the target. Count is the
// specification function, and example.dfy defines it as the number of elements equal to x.
//@ requires v.size() <= 10000
//@ requires i <= v.size()
//@ decreases v.size() - i
//@ ensures result <= v.size() - i
//@ ensures result == Count(v[i..], x)
size_t count_equal(const std::vector<int32_t>& v, size_t i, int32_t x) {
  if (i == v.size()) {
    return 0;
  }
  size_t rest = count_equal(v, i + 1, x);
  if (v[i] == x) {
    return rest + 1;
  }
  return rest;
}
