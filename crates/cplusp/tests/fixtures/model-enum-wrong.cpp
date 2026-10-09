#include <cstdint>

// A contract that a switch does not meet is named at its line, decision 0109.
enum class Kind : uint8_t { Small, Large };

//@ ensures result == (k == Kind::Small ? 1 : 10)
int32_t weight(Kind k) {
  switch (k) {
    case Kind::Small:
      return 1;
    case Kind::Large:
      return 100;
  }
  return 0;
}

//@ ensures result == Kind::Large
Kind pick(bool big) {
  Kind k = Kind::Small;
  if (big) {
    k = Kind::Large;
  }
  return k;
}
