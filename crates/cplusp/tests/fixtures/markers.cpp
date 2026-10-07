#include <cstdint>
#include <iostream>
#include <memory>
#include "../../../../include/cplusp.h"

// A trusted body may hold what a Trusted only row allows, here `new`.
CPLUSP_TRUSTED("allocates with new, and a unique_ptr owns the object at once")
//@ ensures result != nullptr && *result == x
std::unique_ptr<int32_t> make_box(int32_t x) {
  return std::unique_ptr<int32_t>(new int32_t(x));
}

// A trusted body may not hold what a ban row bans.
CPLUSP_TRUSTED("a jump, which the gate bans in every kind of function but plain")
//@ ensures result == x
int32_t jumps(int32_t x) {
  goto done;
done:
  return x;
}

// A plain function is out of the gate's view, its declaration and its body.
CPLUSP_PLAIN("the legacy parser, which has no contract yet")
int legacy_parse(int x) {
  int* p = new int(x);
  int r = *p;
  delete p;
  return r;
}

// Verified code may not call a plain function.
//@ ensures true
int32_t uses_legacy(int32_t x) {
  return legacy_parse(x);
}

// The marker on a declaration covers the definition below it.
CPLUSP_TRUSTED("prints, which only trusted code does")
//@ ensures true
void report(int32_t x);

void report(int32_t x) {
  std::cout << x;
}

// Code with no marker is verified, and every finding in it stands.
int32_t plain_int(int x) {
  return x;
}
