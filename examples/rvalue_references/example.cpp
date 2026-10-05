#include <cstddef>
#include <cstdint>
#include <utility>
#include <vector>

// An rvalue reference parameter takes a value that the caller gives up. The function moves it into a local, and std::move of a local
// or a parameter is the only move allowed. The moved-from vector is never read again. The model treats a move as a copy and the
// source as gone.
//@ requires v.size() <= 0x7FFFFFFFFFFFFFFF
//@ ensures result == old(v.size())
size_t consume(std::vector<int32_t>&& v) {
  std::vector<int32_t> owned = std::move(v);
  return owned.size();
}

//@ ensures result == 3
size_t build_and_consume() {
  std::vector<int32_t> v(3, 0);
  return consume(std::move(v));
}
