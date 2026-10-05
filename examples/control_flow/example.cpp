#include <cstddef>
#include <cstdint>
#include <vector>

// A for loop with an early return, and a switch with a case for every enumerator. The prover follows both. The loop invariant
// says what the loop has seen when it stops, and the decreases clause shows that it ends.
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

enum class Kind : uint8_t { Small, Large };

//@ ensures result == (k == Kind::Small ? 1 : 10)
int32_t weight(Kind k) {
  switch (k) {
    case Kind::Small:
      return 1;
    case Kind::Large:
      return 10;
  }
  // No other value arrives here, because the enum_cast row keeps a value that is no enumerator out. The compiler cannot see
  // that, so it needs this return. The model has no such path.
  return 0;
}
