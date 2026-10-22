#include <cstdint>

// An impure functor in a contract, a call in a branch, and a call of a bound name are refused, decisions 0098 and 0100.
struct Twice {
  int32_t operator()(int32_t x) const {
    int32_t y = 0; y = x;
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

//@ ensures forall t :: 0 <= t < 1 ==> t(x) == x
int32_t shadow(Twice t, int32_t x) {
  return x;
}
