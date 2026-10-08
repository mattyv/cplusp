#include <cstdint>

// Two overloads from one expansion of a macro are two functions, each with its own method, decision 0058. A macro holds no contract,
// so the callers have none. If a call took the wrong overload, its result type would not match, and Dafny would refuse the file.
#define TWO                \
  int32_t p(int32_t x) {   \
    return 1;              \
  }                        \
  int64_t p(int64_t x) {   \
    return 2;              \
  }
TWO

int32_t calls_p32() {
  return p(5);
}

int64_t calls_p64() {
  return p(int64_t{5});
}
