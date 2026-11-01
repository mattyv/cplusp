// The address of a global through a value that is not a constant still changes the global, under a team that loosens
// raw_pointer, decision 0226.
#include <cstdint>
int32_t g_total = 0;
struct P {
  int32_t *p;
  int32_t n;
};
void bump(const P &q) { *q.p += q.n; }
//@ reads g_total
int32_t caller(bool c) {
  int32_t other = 0;
  int32_t *ptr = c ? &g_total : &other;
  P x{ptr, 2};
  bump(x);
  return g_total;
}
