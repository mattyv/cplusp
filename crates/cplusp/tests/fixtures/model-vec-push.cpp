#include <cstddef>
#include <cstdint>
#include <vector>

// push_back adds one element at the end of a vector by reference, decision 0148.
//@ modifies v
//@ ensures v.size() == old(v.size()) + 1
//@ ensures v[old(v.size())] == x
//@ ensures forall j :: 0 <= j < old(v.size()) ==> v[j] == old(v[j])
void append(std::vector<int32_t>& v, int32_t x) {
  v.push_back(x);
}

//@ requires 0 < v.size()
//@ modifies v
//@ ensures v.size() == old(v.size()) + 2
//@ ensures v[v.size() - 1] == v[0]
void echo_first(std::vector<int32_t>& v) {
  int32_t first = v[0];
  v.push_back(1);
  v.push_back(first);
}

//@ modifies v
//@ ensures v.size() == old(v.size()) + n
//@ ensures forall j :: old(v.size()) <= j < v.size() ==> v[j] == 0
void fill(std::vector<int32_t>& v, size_t n) {
  //@ invariant i <= n && v.size() == old(v.size()) + i
  //@ invariant forall j :: old(v.size()) <= j < v.size() ==> v[j] == 0
  for (size_t i = 0; i < n; ++i) {
    v.push_back(0);
  }
}
