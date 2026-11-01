#include <cstdint>

// A pointer to a global inside an object still changes the global, under a team that loosens raw_pointer, decision 0225.
int32_t g_total = 0;

struct P {
  int32_t *p;
  int32_t n;
};

void bump(const P &q) { *q.p += q.n; }

//@ reads g_total
int32_t caller() {
  P x{&g_total, 2};
  bump(x);
  return g_total;
}
