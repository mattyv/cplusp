#include <cstddef>
#include <cstdint>
#include <utility>
#include <vector>

// std::move of a local hands its contents to the callee, and the moved-from vector is never read again. The model treats
// a move as a copy and the source as gone.
//@ ensures result == v.size()
size_t consume(std::vector<int32_t> v) {
  return v.size();
}

//@ ensures result == 3
size_t build_and_consume() {
  std::vector<int32_t> v(3, 0);
  return consume(std::move(v));
}
