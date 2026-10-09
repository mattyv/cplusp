#include <cstddef>
#include <cstdint>
#include <vector>

// Hex literals, exists, and several bound names, decision 0082.
//@ requires v.size() <= 0x7FFF'FFFFull
//@ requires forall i, j :: 0 <= i < j < v.size() ==> v[i] <= v[j]
//@ requires exists k :: 0 <= k < v.size() && v[k] == target
//@ ensures result < v.size() && v[result] == target
size_t find(const std::vector<int32_t>& v, int32_t target) {
  //@ invariant i <= v.size()
  //@ invariant forall k :: 0 <= k < i ==> v[k] != target
  //@ decreases v.size() - i
  for (size_t i = 0; i < v.size(); ++i) {
    if (v[i] == target) {
      return i;
    }
  }
  return 0;
}

//@ requires x < 0x7FFFFFFF
//@ ensures result == x + 1
int32_t next(int32_t x) {
  return x + 1;
}

// true and false in a contract, decision 0084.
//@ ensures result == true || result == false
//@ ensures !(result == false) ==> x > 0
bool positive(int32_t x) {
  return x > 0;
}
