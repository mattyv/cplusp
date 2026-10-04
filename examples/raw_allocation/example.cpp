#include <cstdint>
#include <memory>

// Allocation is trusted. The trusted function allocates and hands the object to a unique_ptr, and its contract says what the
// box holds. The body is in trusted.cpp. The caller uses the box as any unique_ptr, and the prover proves from the contract.
//@ ensures result != nullptr && *result == x
std::unique_ptr<int32_t> make_box(int32_t x);

//@ requires -0x40000000 <= x < 0x40000000
//@ ensures result == 2 * x
int32_t doubled(int32_t x) {
  std::unique_ptr<int32_t> b = make_box(x);
  return *b + *b;
}
