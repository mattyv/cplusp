#include <cstdint>
#include <memory>

// A unique_ptr that the code only reads is an optional, decision 0142. It is the one owner, so nothing else names the object.
//@ ensures result != nullptr && *result == x
std::unique_ptr<int32_t> boxed(int32_t x) {
  return std::make_unique<int32_t>(x);
}

//@ requires p != nullptr
//@ ensures result == *p
int32_t unboxed(const std::unique_ptr<int32_t>& p) {
  return *p;
}

struct Pair {
  int32_t lo;
  int32_t hi;
};

//@ ensures result == (p == nullptr ? 0 : p->hi)
int32_t high(const std::unique_ptr<Pair>& p) {
  if (p == nullptr) {
    return 0;
  }
  return p->hi;
}

//@ requires -1000 <= x <= 1000
//@ ensures result == 2 * x
int32_t round_trip(int32_t x) {
  std::unique_ptr<int32_t> p = boxed(x);
  return unboxed(p) + *p;
}
