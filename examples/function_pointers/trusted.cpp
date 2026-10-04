#include <cstdint>

// Trusted: the function calls its target through a pointer, and the target adds one. The gate refuses a function pointer under
// the function_pointers row, which is the point. Verified code sees only the contract of increment in example.cpp.
int32_t successor(int32_t x) {
  return x + 1;
}

int32_t apply(int32_t (*f)(int32_t), int32_t x) {
  return f(x);
}

int32_t increment(int32_t x) {
  return apply(successor, x);
}
