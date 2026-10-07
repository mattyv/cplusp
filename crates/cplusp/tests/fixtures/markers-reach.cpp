#include <algorithm>
#include <cstdint>
#include <vector>
#include "../../../../include/cplusp.h"

// A destructor runs where no call names it.
struct Guard {
  int32_t v = 0;
  CPLUSP_PLAIN("releases a handle of the old API")
  ~Guard() {}
};

int32_t guarded(int32_t x) {
  Guard g;
  g.v = x;
  return g.v;
}

// The library calls an operator that the file wrote.
struct Key {
  int32_t k = 0;
  CPLUSP_PLAIN("the order of the old API")
  bool operator<(const Key& o) const {
    return k < o.k;
  }
};

void order(std::vector<Key>& keys) {
  std::sort(keys.begin(), keys.end());
}

// A virtual call reaches each override, and a plain override is refused where it overrides.
struct Shape {
  virtual ~Shape() = default;
  //@ ensures true
  virtual int32_t area() const = 0;
};

struct Legacy : Shape {
  CPLUSP_PLAIN("an old shape")
  int32_t area() const override {
    return 1;
  }
};

int32_t area_of(const Shape& s) {
  return s.area();
}

// A trusted body may run plain code.
CPLUSP_TRUSTED("wraps the old API")
//@ ensures result == x
int32_t wrapped(int32_t x) {
  Guard g;
  g.v = x;
  return g.v;
}
