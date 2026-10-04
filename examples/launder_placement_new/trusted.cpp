#include <cstdint>
#include <new>

// Trusted: std::launder gives a pointer to the object that now lives at an address. Lifetime games are beyond the prover, and the
// gate refuses std::launder under the launder_placement_new row, which is the point. Verified code sees only the contract.
int32_t read_back(const int32_t* p) {
  return *std::launder(p);
}
