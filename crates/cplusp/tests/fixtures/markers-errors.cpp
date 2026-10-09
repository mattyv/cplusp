#include <cstdint>
#include "../../../../include/cplusp.h"

CPLUSP_TRUSTED("vector intrinsics")
int32_t fast_sum(int32_t a, int32_t b);

CPLUSP_TRUSTED("")
//@ ensures result == a
int32_t no_reason(int32_t a);

CPLUSP_PLAIN("   ")
int32_t blank_reason(int32_t a);

CPLUSP_TRUSTED("the first kind")
//@ ensures result == a
int32_t two_kinds(int32_t a);

CPLUSP_PLAIN("the second kind")
int32_t two_kinds(int32_t a);

[[clang::annotate("cplusp:trustd", "a typo")]]
//@ ensures result == a
int32_t typo(int32_t a);

struct CPLUSP_TRUSTED("a class is no function") Box {
  int32_t v;
};

[[clang::annotate("cplusp:x\ty")]]
//@ ensures result == a
int32_t tabbed(int32_t a);

CPLUSP_ASSUME("one statement")
int32_t assumed(int32_t a);

CPLUSP_TRUSTED("reads a register\nok: proved")
//@ ensures result <= 255
int32_t forged(int32_t a);
