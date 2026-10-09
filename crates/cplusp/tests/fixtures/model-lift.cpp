#include <cstdint>

// A call inside an expression runs before its statement, when C++ always evaluates it once, decision 0104.
//@ requires x < 1000
//@ ensures result == x + 1
int32_t inc(int32_t x) {
  return x + 1;
}

//@ requires x < 998
//@ ensures result == x + 3
int32_t three(int32_t x) {
  return inc(inc(x)) + 1;
}

//@ requires x < 500
//@ ensures result == (x + 1 > 100)
bool big(int32_t x) {
  return inc(x) > 100;
}

//@ requires -1000 < x && x < 499
//@ ensures result == 2 * x + 2
int32_t twice(int32_t x) {
  int32_t y = inc(x) + inc(x);
  if (inc(y) > 0) {
    return y;
  }
  return y;
}

// A call in an else-if condition runs only where the condition before it is false.
//@ requires x > 0
//@ ensures result == x
int32_t pos(int32_t x) {
  return x;
}

//@ requires x < 1000
//@ ensures (x <= 0 && result == 0) || (x > 0 && result == x + 7)
int32_t elseif(int32_t x) {
  if (x <= 0) {
    return 0;
  } else if (pos(x) > 1000000) {
    return x + 7;
  }
  return x + 7;
}

// A call in the start and in the step of a for loop runs at its place.
//@ requires 0 < n && n < 100
//@ ensures result == n
int32_t forstartstep(int32_t n) {
  int32_t s = 0;
  //@ invariant 1 <= i && i <= n + 1 && s == i - 1
  //@ decreases n + 1 - i
  for (int32_t i = pos(1); i <= n; i = i + pos(1)) {
    s = s + 1;
  }
  return s;
}

// A constructor call inside an expression keeps its requires line, decision 0105.
struct Q {
  int32_t v;

  //@ requires a > 0
  //@ ensures v == a
  explicit Q(int32_t a) : v(a) {}
};

//@ requires x > 0
//@ ensures result == x
int32_t built(int32_t x) {
  return Q(x).v + 0;
}
