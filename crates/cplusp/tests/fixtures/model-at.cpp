#include <array>
#include <cstddef>
#include <cstdint>
#include <vector>

// `v.at(i)` of a read-only sequence is `v[i]`, decision 0139. The prover proves the index in range, so `at` never throws.
//@ requires i < v.size()
//@ ensures result == v[i]
int32_t element(const std::vector<int32_t>& v, size_t i) {
  return v.at(i);
}

//@ ensures result == a[1]
int32_t second(const std::array<int32_t, 3>& a) {
  return a.at(1);
}
