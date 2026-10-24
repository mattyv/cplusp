#include <cstddef>
#include <cstdint>
#include <utility>
#include <vector>

// A vector that a function takes by rvalue reference and moves into a local, a move of a local vector, and a vector of n copies
// of a value, decision 0185.
//@ requires v.size() <= 0x7FFFFFFFFFFFFFFF
//@ modifies v
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

//@ requires n <= 100
//@ ensures result == x
int32_t filled(size_t n, int32_t x) {
  std::vector<int32_t> v(n + 1, x);
  return v[n];
}

//@ ensures result == 2
size_t moved_local() {
  std::vector<int32_t> a(2, 7);
  std::vector<int32_t> b = std::move(a);
  return b.size();
}

// The move reads the vector as the body leaves it, after the write.
//@ requires v.size() <= 0x7FFFFFFFFFFFFFFF && v.size() > 0
//@ modifies v
//@ ensures result == 5
int32_t written_first(std::vector<int32_t>&& v) {
  v[0] = 5;
  std::vector<int32_t> owned = std::move(v);
  return owned[0];
}
