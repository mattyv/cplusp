#include <cstddef>
#include <cstdint>
#include <utility>
#include <vector>

// A vector by rvalue reference that the modifies line does not name, and a move out of a vector by value, decision 0185. by_value proves since 0194.
//@ requires v.size() <= 0x7FFFFFFFFFFFFFFF
//@ ensures result == old(v.size())
size_t unlisted(std::vector<int32_t>&& v) {
  std::vector<int32_t> owned = std::move(v);
  return owned.size();
}

//@ ensures true
size_t by_value(std::vector<int32_t> v) {
  std::vector<int32_t> owned = std::move(v);
  return owned.size();
}

//@ ensures true
size_t one_count() {
  std::vector<int32_t> v(3);
  return v.size();
}

//@ ensures true
size_t two_values() {
  std::vector<int32_t> v{3, 0};
  return v.size();
}

//@ requires v.size() <= 0x7FFFFFFFFFFFFFFF
//@ modifies v
//@ ensures result.size() == old(v.size()) && v.size() == old(v.size())
std::vector<int32_t> handed_on(std::vector<int32_t>&& v) {
  return std::move(v);
}

//@ requires v.size() <= 0x7FFFFFFFFFFFFFFF
//@ modifies v
//@ ensures result == old(v.size()) && v.size() == old(v.size())
size_t assigned(std::vector<int32_t>&& v) {
  std::vector<int32_t> w(1, 0);
  w = std::move(v);
  return w.size();
}

//@ ensures true
std::vector<int32_t> given() {
  return std::vector<int32_t>(3, 7);
}
