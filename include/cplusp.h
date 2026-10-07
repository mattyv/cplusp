// The markers of docs/plan.md, section "Markers and the escape hatch". They are the only way a function changes kind.
// A new function is verified by default. CPLUSP_TRUSTED keeps a contract and skips the proof, with a reason.
// CPLUSP_PLAIN opts a function or a class out, and verified code cannot call it. CPLUSP_ASSUME covers one statement.
// The gate reads them, decisions 0039 and 0047. A finding takes the kind of the function that holds it. CPLUSP_ASSUME
// waits until a case needs it. Clang 18 takes the attribute on no statement.
#pragma once

#ifdef __clang__
#define CPLUSP_VERIFIED [[clang::annotate("cplusp:verified")]]
#define CPLUSP_TRUSTED(why) [[clang::annotate("cplusp:trusted", why)]]
#define CPLUSP_PLAIN(why) [[clang::annotate("cplusp:plain", why)]]
#define CPLUSP_ASSUME(why) [[clang::annotate("cplusp:assume", why)]]
#else
#define CPLUSP_VERIFIED
#define CPLUSP_TRUSTED(why)
#define CPLUSP_PLAIN(why)
#define CPLUSP_ASSUME(why)
#endif
