#include <algorithm>
#include <cstdint>
#include <vector>

// std::sort is on the trusted list, and its contract is a sorted permutation. The function sorts a copy and reads its first element,
// so the vector of the caller stays as it was. The proof that the result is the smallest comes from the contract of sort alone.
//@ requires !v.empty()
//@ ensures forall j :: 0 <= j < v.size() ==> result <= v[j]
//@ ensures exists j :: 0 <= j < v.size() && v[j] == result
int32_t minimum(const std::vector<int32_t>& v) {
  std::vector<int32_t> sorted = v;
  std::sort(sorted.begin(), sorted.end());
  return sorted[0];
}

// std::count_if is on the trusted list too. The lambda has no capture and goes straight to the algorithm. Negatives is the
// specification function, and example.dfy defines it as the number of elements below zero.
//@ requires v.size() <= 0x7FFFFFFF
//@ ensures result == Negatives(v)
int32_t count_negative(const std::vector<int32_t>& v) {
  return static_cast<int32_t>(std::count_if(v.begin(), v.end(), [](int32_t x) { return x < 0; }));
}
