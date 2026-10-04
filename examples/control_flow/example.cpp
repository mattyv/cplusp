#include <cstddef>
#include <cstdint>
#include <vector>

// A for loop with an early return, and a switch with a case for every enumerator. The prover follows both. The contract says
// what the loop saw before it stopped: everything before the result differs from the target.
//@ ensures result <= v.size()
//@ ensures result < v.size() ==> v[result] == target
//@ ensures forall j < result: v[j] != target
size_t find(const std::vector<int32_t>& v, int32_t target) {
  for (size_t i = 0; i < v.size(); ++i) {
    if (v[i] == target) {
      return i;
    }
  }
  return v.size();
}

enum class Kind : uint8_t { Small, Large };

//@ ensures result == (k == Kind::Small ? 1 : 10)
int32_t weight(Kind k) {
  switch (k) {
    case Kind::Small:
      return 1;
    case Kind::Large:
      return 10;
  }
  return 0;
}
