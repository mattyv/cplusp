// The address of a global through a value that is not a constant still changes the global, under a team that loosens
// raw_pointer, decision 0226.
#include <cstdint>
#include <vector>
int32_t g_total = 0;
struct P {
  int32_t *p;
  int32_t n;
};
void bump(const P &q) { *q.p += q.n; }
//@ reads g_total
int32_t caller() {
  std::vector<P> v{{&g_total, 2}};
  bump(v[0]);
  return g_total;
}
