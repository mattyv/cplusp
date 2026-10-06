#include <cstdint>

// Trusted: the legacy function takes a non-const reference but only reads. The const_cast hands it the const argument. The gate
// refuses const_cast under the reinterpret_const_cast row, which is the point. Verified code sees only the contract.
// The declaration in example.cpp carries the CPLUSP_TRUSTED marker.
//@ ensures x == old(x)
int32_t legacy_read(int32_t& x);

int32_t read_through(const int32_t& x) {
  return legacy_read(const_cast<int32_t&>(x));
}
