#include <cstdint>

// Locals, casts and calls, decision 0058. Each refusal is at its line, and the model still resolves in Dafny.
int32_t declared(int32_t x);

//@ ensures result == x
int32_t id(int32_t x) {
  return x;
}

int32_t inside(int32_t x) {
  return id(x) + 0;
}

int32_t nested(int32_t x) {
  return id(id(x));
}

int32_t to_declared(int32_t x) {
  return declared(x);
}

struct T {
  static int32_t one() { return 1; }
};

int32_t to_member() {
  return T::one();
}

int32_t twice(int32_t x) {
  int32_t y = x;
  if (y > 0) {
    int32_t y = 1;
    return y;
  }
  return y;
}

int32_t shadow(int32_t x) {
  if (x > 0) {
    int32_t x = 2;
    return x;
  }
  return x;
}

int32_t from_bool(bool b) {
  int32_t i = b;
  return i;
}

int32_t no_start() {
  int32_t z;
  return 0;
}

int32_t two_names() {
  int32_t p = 1, q = 2;
  return p;
}

// A bad contract line keeps the method with no contract, so a caller still has a model.
//@ ensures result = x
int32_t bad_contract(int32_t x) {
  return x;
}

int32_t calls_bad(int32_t x) {
  int32_t r = bad_contract(x);
  return r;
}

// A refused body keeps the method with no contract and no body, so a caller proves nothing from it.
//@ ensures result == 0
int32_t refused_body(int32_t x) {
  return x << 2;
}

int32_t calls_refused(int32_t x) {
  return refused_body(x);
}

// A default argument has no rule. The refusal is at the line of the call.
int32_t add(int32_t x, int32_t y = 5) {
  return x;
}

int32_t defaulted() {
  return add(1);
}

// An assignment to a local, which decision 0061 models.
int32_t assigns(int32_t x) {
  int32_t y = x;
  y = 2;
  return y;
}
