#include <cstdint>
#include <cstdio>
#include "../../../../include/cplusp.h"

// A pointer to a plain object counts as the object, decision 0053. The library reads every byte of it.
struct CPLUSP_PLAIN("an old record") Record {
  int count = 0;
};

void dump(const Record& r, std::FILE* f) {
  std::fwrite(&r, sizeof r, 1, f);
}

// A friend in a plain type is plain, unless it has a marker of its own. A trusted friend keeps its contract.
struct CPLUSP_PLAIN("an old pair") Pair {
  int first = 0;
  friend int twice_of(const Pair& p) {
    return p.first * 2;
  }
  CPLUSP_TRUSTED("reads the first of the old pair")
  //@ ensures true
  friend int32_t first_of(const Pair& p) {
    return p.first;
  }
};

// Verified code calls the trusted friend, and not the plain one.
int32_t through_trusted(const Pair& p) {
  return first_of(p);
}

int32_t through_plain(const Pair& p) {
  return twice_of(p);
}
