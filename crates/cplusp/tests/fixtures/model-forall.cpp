#include <cstdint>
#include <vector>

// A forall binds an exact integer, decision 0067, even when the body does not use it or a second forall binds the same name.
//@ ensures forall j :: x == x
int32_t unused(int32_t x) {
  return x;
}

//@ ensures forall j :: forall j :: 0 <= j < v.size() ==> v[j] == v[j]
int32_t shadowed(const std::vector<int32_t>& v) {
  return 0;
}
