#include <cstdint>

// A pointer with no const, and a test of a pointer as a bool, have no rule yet, decision 0140.
//@ modifies p
int32_t write(int32_t* p) {
  return 0;
}

int32_t test(const int32_t* p) {
  if (p) {
    return 1;
  }
  return 0;
}

// Two pointers do not compare, in code and in a contract, decision 0141. Nor does this.
bool same(const int32_t* p, const int32_t* q) {
  return p == q;
}

//@ requires p == q
int32_t equal(const int32_t* p, const int32_t* q) {
  return 0;
}

//@ requires p < q
int32_t before(const int32_t* p, const int32_t* q) {
  return 0;
}

struct S {
  int32_t v;
  bool none() const {
    return this == nullptr;
  }
};
