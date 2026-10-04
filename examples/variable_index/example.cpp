#include <cstddef>
#include <cstdint>
#include <vector>

// A variable index is safe when the contract keeps it in range, and the caller proves the range. A write says which
// element changes and that every other element keeps its value.
//@ requires i < v.size()
//@ ensures result == v[i]
int32_t read_at(const std::vector<int32_t>& v, size_t i) {
  return v[i];
}

//@ requires i < v.size()
//@ modifies v
//@ ensures v.size() == old(v.size())
//@ ensures v[i] == x
//@ ensures forall j < v.size(): j != i ==> v[j] == old(v[j])
void write_at(std::vector<int32_t>& v, size_t i, int32_t x) {
  v[i] = x;
}
