#include <algorithm>
#include <cstdint>
struct S { int32_t x; int32_t y; };
S g_s{1, 2};
//@ reads g_s
int32_t reader() { return std::max(g_s.x, g_s.y); }
