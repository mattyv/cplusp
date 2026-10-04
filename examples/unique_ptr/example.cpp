#include <cstdint>
#include <memory>

// A unique_ptr has one owner. The prover models it as a reference that may be null, so the contract says when it is not.
// The function that makes the box promises a fresh one, and the function that reads it needs one that is not null.
//@ ensures result != nullptr && *result == x
std::unique_ptr<int32_t> boxed(int32_t x) {
  return std::make_unique<int32_t>(x);
}

//@ requires p != nullptr
//@ ensures result == *p
int32_t unboxed(const std::unique_ptr<int32_t>& p) {
  return *p;
}

//@ ensures result == x
int32_t round_trip(int32_t x) {
  std::unique_ptr<int32_t> p = boxed(x);
  return unboxed(p);
}
