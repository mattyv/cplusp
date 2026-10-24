#include <cstddef>
#include <cstdint>
#include <utility>
#include <vector>

// A moved-from vector has any value, so a claim about it fails. A vector of n copies holds the value it copies, decision 0185.
//@ requires v.size() <= 0x7FFFFFFFFFFFFFFF
//@ modifies v
//@ ensures result == old(v.size()) && v.size() == old(v.size())
size_t keeps(std::vector<int32_t>&& v) {
  std::vector<int32_t> owned = std::move(v);
  return owned.size();
}

//@ ensures result == 1
int32_t filled() {
  std::vector<int32_t> v(3, 0);
  return v[2];
}

//@ requires v.size() <= 0x7FFFFFFFFFFFFFFF && v.size() > 0 && v[0] != 5
//@ modifies v
//@ ensures result == old(v[0])
int32_t written_first(std::vector<int32_t>&& v) {
  v[0] = 5;
  std::vector<int32_t> owned = std::move(v);
  return owned[0];
}

//@ requires v.size() <= 0x7FFFFFFFFFFFFFFF
//@ modifies v
//@ ensures v.size() == 0
size_t emptied(std::vector<int32_t>&& v) {
  std::vector<int32_t> owned = std::move(v);
  return owned.size();
}
