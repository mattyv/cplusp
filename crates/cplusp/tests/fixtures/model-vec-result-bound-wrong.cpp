#include <cstdint>
#include <vector>

// A vector that may outgrow the bound has its own sentence at the return, decision 0164. A local from a call is a sequence like
// a local copy, so its failure is at the return too.
//@ ensures result.size() == v.size()
std::vector<int32_t> same(const std::vector<int32_t>& v) {
  return v;
}

//@ ensures result.size() == v.size() + 1
std::vector<int32_t> grow_copy(const std::vector<int32_t>& v) {
  std::vector<int32_t> x = v;
  x.push_back(1);
  return x;
}

//@ ensures result.size() == v.size() + 1
std::vector<int32_t> grow_call(const std::vector<int32_t>& v) {
  std::vector<int32_t> x = same(v);
  x.push_back(1);
  return x;
}
