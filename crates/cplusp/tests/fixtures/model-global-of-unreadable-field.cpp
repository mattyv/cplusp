#include <cstdint>
struct W { int32_t ñ; };
W g_w{};
//@ reads g_w
//@ ensures result == 1
int32_t g() { return 1; }
