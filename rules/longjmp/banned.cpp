#include <cstdint>
#include <csetjmp>
#include <type_traits>

// A jmp_buf is an array. Passing one decays it, which another rule reports.
// A pointer to its first element does not decay, so each call below breaks one rule only.
using JmpPtr = std::decay_t<std::jmp_buf>;

void bail(JmpPtr env) {
  std::longjmp(env, 1);  // BANNED
}

int32_t enter(JmpPtr env) {
  return setjmp(env);  // BANNED
}
