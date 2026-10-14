#include <algorithm>
#include <cstdint>
#include <vector>

// A lambda passed straight to a std algorithm, capturing by value and not mutable, is a pure function of its argument and its
// captures. The prover models the algorithm and the lambda together as CountIf over the sequence, decision 0149. Count is the
// specification in example.spec.dfy, and example.dfy defines it as the number of elements above k.
//@ requires v.size() <= 0x7FFFFFFF
//@ ensures result == Count(v, k)
int32_t count_above(const std::vector<int32_t>& v, int32_t k) {
  return static_cast<int32_t>(std::count_if(v.begin(), v.end(), [k](int32_t x) { return x > k; }));
}
