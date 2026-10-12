#include <cstdint>

// A parameter of type `const T*` is an optional of T, decision 0140. Null is no value, and `*p` reads the value.
//@ requires p != nullptr
//@ ensures result == *p
int32_t read(const int32_t* p) {
  return *p;
}

//@ ensures result == (p == nullptr ? fallback : *p)
int32_t read_or(const int32_t* p, int32_t fallback) {
  if (p == nullptr) {
    return fallback;
  }
  return *p;
}

struct Pair {
  int32_t lo;
  int32_t hi;
};

//@ requires nullptr != q
//@ ensures result == q->hi
int32_t high(const Pair* q) {
  return q->hi;
}

// A caller passes the address of a local, a pointer it has, or nullptr.
//@ requires -1000 <= x <= 1000
//@ ensures result == x + 7
int32_t caller(int32_t x) {
  int32_t y = 7;
  return read(&x) + read_or(nullptr, 0) + read_or(&y, 0);
}
