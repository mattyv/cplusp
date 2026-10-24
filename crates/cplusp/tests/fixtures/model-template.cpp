#include <cstdint>

// A function template is a function for each type that the file uses it at, decision 0180.
//@ ensures result >= a && result >= b && (result == a || result == b)
template <typename T>
T larger(T a, T b) {
  return a < b ? b : a;
}

// A template that calls a template makes an instance of the callee at its own type.
//@ ensures result >= a && result >= b && result >= c
template <typename T>
T largest(T a, T b, T c) {
  return larger(larger(a, b), c);
}

// Two type parameters.
//@ ensures result == a
template <typename A, typename B>
A first(A a, B b) {
  return b ? a : a;
}

// Two templates of one name are two functions at one type. They are numbered as overloads are.
//@ ensures result == a
template <typename T>
T pick(T a) {
  return a;
}

//@ ensures result == b
template <typename T>
T pick(T a, T b) {
  return b;
}

//@ ensures result == b
int32_t pick_of(int32_t a, int32_t b) {
  return pick(pick(a), b);
}

//@ ensures result >= a && result >= b
int32_t larger32(int32_t a, int32_t b) {
  return larger(a, b);
}

//@ ensures result >= a && result >= b
uint8_t larger8(uint8_t a, uint8_t b) {
  return larger(a, b);
}

// An explicit type argument names the same instance as a deduced one.
//@ ensures result >= a
int32_t larger_named(int32_t a, int32_t b) {
  return larger<int32_t>(a, b);
}

//@ ensures result >= a && result >= c
int64_t largest64(int64_t a, int64_t b, int64_t c) {
  return largest(a, b, c);
}

//@ ensures result == a
int32_t first_of(int32_t a, bool b) {
  return first(a, b);
}
