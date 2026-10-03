#include <algorithm>
#include <cstdint>
#include <vector>

//@ modifies v
//@ ensures v is sorted and a permutation of old(v)
void sort_in_place(std::vector<int32_t>& v) {
  std::sort(v.begin(), v.end());
}
