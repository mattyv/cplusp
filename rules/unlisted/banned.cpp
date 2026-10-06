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

//@ requires p != nullptr
void done(int32_t* p);

// Attributes are not node kinds, so they have a list of their own. A cleanup attribute runs a hidden call at scope exit.
int32_t with_cleanup() {
  int32_t x __attribute__((cleanup(done))) = 0;  // BANNED
  return x;
}

[[gnu::pure]] int32_t promised_pure(int32_t x);  // BANNED

struct __attribute__((may_alias)) Alias {  // BANNED
  int32_t v;
};

// A qualifier is no node kind and no attribute. __restrict promises the compiler that two pointers never alias.
void restrict_ptr(int32_t* __restrict a);  // BANNED

// The same qualifier on a member function restricts `this`.
struct Restricted {
  void f() __restrict;  // BANNED
};
