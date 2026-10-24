#include <cstddef>
#include <cstdint>
#include <utility>
#include <vector>

// A team that loosens rvalue_references reads a vector after its move. The model keeps no value for it, decision 0185.
//@ requires v.size() <= 0x7FFFFFFFFFFFFFFF
//@ modifies v
//@ ensures result == old(v.size())
size_t consume(std::vector<int32_t>&& v) {
  std::vector<int32_t> owned = std::move(v);
  return owned.size();
}

//@ ensures !result
bool local_after() {
  std::vector<int32_t> a(2, 7);
  std::vector<int32_t> b = std::move(a);
  return a.empty();
}

//@ ensures !result
bool caller_after() {
  std::vector<int32_t> v(3, 0);
  size_t n = consume(std::move(v));
  return v.empty() && n == 3;
}
