#include <cstdint>
#include <span>
#include <vector>

// A span of const over data that a callee changes, decision 0067. g has no model, and its body writes the global that s views.
std::vector<int32_t> gv = {1, 2, 3};
int32_t g() {
  gv[0] = 7;
  return 0;
}

//@ requires s.size() > 0
//@ ensures result == 0
int32_t f(std::span<const int32_t> s) {
  int32_t a = s[0];
  int32_t t = g();
  int32_t b = s[0];
  return a - b;
}
