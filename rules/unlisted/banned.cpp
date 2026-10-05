#include <cstdint>

// Constructs no row names. Each is a kind of node outside the lists, so the gate refuses it without a rule of its own.
int32_t statement_expression(int32_t x) {
  return ({ int32_t t = x; t + 1; });  // BANNED
}

int32_t lane(int32_t x) {
  typedef int32_t four __attribute__((vector_size(16)));  // BANNED
  four v = {x, x, x, x};
  return v[0];
}

double real_part() {
  _Complex double z = 1.0;  // BANNED
  return __real__ z;
}

int32_t same_type(int32_t x) {
  __typeof__(x) y = x;  // BANNED
  return y;
}

int32_t either(int32_t x) {
  return x ?: 1;  // BANNED
}

int32_t first_of_vla(int32_t n) {
  int32_t a[n];  // BANNED
  a[0] = 1;
  return a[0];
}
