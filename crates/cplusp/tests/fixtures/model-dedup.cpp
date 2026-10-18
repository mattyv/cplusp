#include <cstddef>
#include <cstdint>
#include <vector>

// One failure that Dafny reports twice is printed once, decision 0155.
//@ modifies v
void grow(std::vector<int32_t>& v) {
  v.push_back(1);
  //@ invariant i <= v.size()
  for (size_t i = 0; i < v.size(); ++i) {
    v[i] = 0;
  }
}
