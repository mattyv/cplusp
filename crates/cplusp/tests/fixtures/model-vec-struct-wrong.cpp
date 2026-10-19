#include <cstdint>
#include <vector>

// A result that is not what the contract says fails at its return, decision 0163.
//@ requires v.size() <= 100
//@ ensures result.size() == v.size()
std::vector<int32_t> appended(const std::vector<int32_t>& v) {
  std::vector<int32_t> out = v;
  out.push_back(0);
  return out;
}
