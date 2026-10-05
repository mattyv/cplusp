// The markers of docs/plan.md, section "Markers and the escape hatch". They are the only way a function changes kind.
// A new function is verified by default. CPLUSP_TRUSTED keeps a contract and skips the proof, with a reason.
// CPLUSP_PLAIN opts a function out, and verified code cannot call it. CPLUSP_ASSUME covers one statement.
// The gate does not read the markers yet, so every function counts as verified today. The attribute is kept so
// that it will, and so that the examples show the shape the bot writes.
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
