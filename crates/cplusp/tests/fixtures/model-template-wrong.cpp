#include <cstdint>

// A contract that holds at one type and fails at another, and a contract that fails at each type, decision 0180.
//@ requires 0 <= a && a < 2000000000
//@ ensures result == a + a
template <typename T>
T twice(T a) {
  return a + a;
}

//@ ensures result > a
template <typename T>
T same(T a) {
  return a;
}

//@ requires 0 <= a && a < 2000000000
//@ ensures result == a + a
int64_t twice64(int64_t a) {
  return twice(a);
}

//@ requires 0 <= a && a < 2000000000
//@ ensures result == a + a
int32_t twice32(int32_t a) {
  return twice(a);
}

//@ requires 0 <= a && a < 2000000000
//@ ensures result == a + a
uint32_t twiceu32(uint32_t a) {
  return twice(a);
}

//@ ensures result > a
int32_t same32(int32_t a) {
  return same(a);
}

//@ ensures result > a
int64_t same64(int64_t a) {
  return same(a);
}

// An explicit instantiation is an instance, and it proves too.
//@ ensures result < a
template <typename T>
T keep(T a) {
  return a;
}

template int32_t keep<int32_t>(int32_t);

// One line that fails at two types, with a sentence for each type.
//@ ensures result == a + a
template <typename T>
T doubled(T a) {
  return a + a;
}

int32_t doubled32(int32_t a) {
  return doubled(a);
}

uint32_t doubledu32(uint32_t a) {
  return doubled(a);
}

// Two checks on one line, in each of two instances with one sentence.
//@ ensures true
template <typename A, typename B>
A triple(A a, B b) {
  return a + a + a;
}

int32_t triple_b(int32_t a, bool b) {
  return triple(a, b);
}

int32_t triple_u(int32_t a, uint8_t b) {
  return triple(a, b);
}
