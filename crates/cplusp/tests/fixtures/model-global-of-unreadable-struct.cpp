#include <cstdint>
struct Pöint { int32_t x; };
struct Wrap { Pöint p; };
Wrap g_w{};
//@ reads g_w
//@ ensures result == 1
int32_t g() { return 1; }
