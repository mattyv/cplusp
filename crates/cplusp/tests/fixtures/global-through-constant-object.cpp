// A constant global of the file that holds the address of a global changes the global through a call, under a team that
// loosens raw_pointer, decision 0228.
#include <cstdint>
int32_t g_total = 0;
struct Holder { int32_t *p; };
const Holder g_h{&g_total};
void bump4(const Holder &h) { *h.p += 1; }
//@ reads g_total
int32_t caller() {
  bump4(g_h);
  return g_total;
}
