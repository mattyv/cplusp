#include <cstddef>
#include <cstdint>
#include <vector>

// A vector by reference that the function writes takes its value in and gives it back, decision 0145.
//@ requires i < v.size()
//@ modifies v
//@ ensures v.size() == old(v.size())
//@ ensures v[i] == x
//@ ensures forall j :: 0 <= j < v.size() ==> (j != i ==> v[j] == old(v[j]))
void write_at(std::vector<int32_t>& v, size_t i, int32_t x) {
  v[i] = x;
}

//@ requires i < v.size() && j < v.size()
//@ modifies v
//@ ensures v.size() == old(v.size())
//@ ensures v[i] == old(v[j]) && v[j] == old(v[i])
void swap_at(std::vector<int32_t>& v, size_t i, size_t j) {
  int32_t t = v[i];
  v[i] = v[j];
  v[j] = t;
}

//@ modifies v
//@ ensures v.size() == old(v.size())
//@ ensures forall k :: 0 <= k < v.size() ==> v[k] == 0
void clear_all(std::vector<int32_t>& v) {
  //@ invariant i <= v.size() && v.size() == old(v.size())
  //@ invariant forall k :: 0 <= k < i ==> v[k] == 0
  for (size_t i = 0; i < v.size(); ++i) {
    v[i] = 0;
  }
}
