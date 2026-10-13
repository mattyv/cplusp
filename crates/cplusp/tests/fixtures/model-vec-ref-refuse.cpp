#include <cstddef>
#include <cstdint>
#include <vector>

// A vector by reference that the modifies line does not name, push_back, a compound write, and a vector of bool, have no rule,
// decision 0145.
void unnamed(std::vector<int32_t>& v) {
}

//@ modifies v
void append(std::vector<int32_t>& v, int32_t x) {
  v.push_back(x);
}

//@ requires 0 < v.size()
//@ modifies v
void add(std::vector<int32_t>& v) {
  v[0] += 1;
}

//@ modifies v
void flags(std::vector<bool>& v) {
}
