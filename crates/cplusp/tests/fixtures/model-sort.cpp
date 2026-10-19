#include <algorithm>
#include <cstdint>
#include <vector>

// std::sort of a vector of integers is StdSort, decision 0161. After the call no later element is below an earlier one, and the
// length stays the same.
//@ requires v.size() >= 2
//@ ensures result
bool first_two_ordered(const std::vector<int32_t>& v) {
  std::vector<int32_t> sorted = v;
  std::sort(sorted.begin(), sorted.end());
  return sorted[0] <= sorted[1];
}

//@ ensures result == v.size()
uint64_t same_length(const std::vector<int32_t>& v) {
  std::vector<int32_t> sorted = v;
  std::sort(sorted.begin(), sorted.end());
  return sorted.size();
}

//@ modifies v
//@ ensures v.size() == old(v.size())
//@ ensures forall i, j :: 0 <= i < j < v.size() ==> v[i] <= v[j]
void sort_in_place(std::vector<uint8_t>& v) {
  std::sort(v.begin(), v.end());
}
