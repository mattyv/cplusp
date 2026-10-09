#include <cstdint>

// A functor whose operator() is not pure in a contract, and a call in a branch, are refused at their lines, decision 0098.
struct Twice {
  int32_t operator()(int32_t x) const {
    int32_t y = x;
    return y;
  }
};

//@ ensures result == t(x)
int32_t use_impure(Twice t, int32_t x) {
  return x;
}

int32_t half(int32_t x) {
  return x / 2;
}

int32_t call_in_branch(int32_t x) {
  return x > 0 ? half(x) : 0;
}
