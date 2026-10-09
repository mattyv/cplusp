#include <cstdint>
#include "../../../../include/cplusp.h"

// A static member, a namespace constant, an unnamed namespace and a local constant hide a constant of the file with the same name,
// decision 0107.
constexpr int32_t kScale = 10;
constexpr int32_t k = 10;
constexpr int32_t j = 10;
constexpr int32_t m = 10;

struct Fixed {
  static constexpr int32_t kScale = 3;
  int32_t n;
  //@ ensures result == kScale
  int32_t get() const {
    return 10;
  }
};

namespace ns {
constexpr int32_t k = 3;
//@ ensures result == k
int32_t get() {
  return 10;
}
}

namespace outer {
namespace {
constexpr int32_t j = 3;
}
//@ ensures result == j
int32_t get() {
  return 10;
}
}

CPLUSP_TRUSTED("holds a local struct")
//@ ensures result == 10
int32_t host() {
  constexpr int32_t k = 3;
  struct Local {
    int32_t n;
    //@ ensures result == k
    int32_t get() const {
      return 10;
    }
  };
  return Local{0}.get();
}

// In C++, m here has two meanings, so the contract has no one constant m.
namespace {
constexpr int32_t m = 3;
}
//@ ensures result == m
int32_t both() {
  return 10;
}

// An inline namespace also gives n two meanings here.
constexpr int32_t n = 10;
inline namespace v1 {
constexpr int32_t n = 3;
}
//@ ensures result == n
int32_t inline_both() {
  return 10;
}
