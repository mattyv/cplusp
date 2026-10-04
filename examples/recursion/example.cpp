#include <cstddef>
#include <cstdint>
#include <vector>

// A recursion needs a decreases clause, the measure that gets smaller at each call, and the prover proves it. It also needs a bound
// on the depth, since the stack is finite. The bound on v.size() is that bound, an assumption about the target.
//@ requires v.size() <= 10000
//@ requires i <= v.size()
//@ decreases v.size() - i
//@ ensures result <= v.size() - i
//@ ensures result == the number of j in [i, v.size()) with v[j] == x
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
