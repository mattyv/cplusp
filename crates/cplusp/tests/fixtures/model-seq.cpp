#include <cstddef>
#include <cstdint>
#include <span>
#include <vector>

// Read-only sequences, decision 0064: find from examples/control_flow, and a test over a span.
//@ ensures result <= v.size()
//@ ensures result < v.size() ==> v[result] == target
//@ ensures forall j :: 0 <= j < result ==> v[j] != target
size_t find(const std::vector<int32_t>& v, int32_t target) {
  //@ invariant i <= v.size()
  //@ invariant forall j :: 0 <= j < i ==> v[j] != target
  //@ decreases v.size() - i
  for (size_t i = 0; i < v.size(); ++i) {
    if (v[i] == target) {
      return i;
    }
  }
  return v.size();
}

//@ ensures result == forall j :: 0 <= j < s.size() ==> s[j] < k
bool all_below(std::span<const uint8_t> s, uint8_t k) {
  //@ invariant i <= s.size()
  //@ invariant forall j :: 0 <= j < i ==> s[j] < k
  //@ decreases s.size() - i
  for (size_t i = 0; i < s.size(); ++i) {
    if (s[i] >= k) {
      return false;
    }
  }
  return true;
}
