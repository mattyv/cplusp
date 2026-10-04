#include <cstdint>

// Trusted: a status register that the hardware writes. The compiler must read it every time, so it is volatile, and the gate
// refuses volatile under the volatile row, which is the point. Verified code sees only the range in the contract.
volatile uint32_t status_register = 0;

uint32_t read_status() {
  return status_register & 0xFFu;
}
