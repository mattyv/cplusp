#include <atomic>
#include <cstdint>

// Trusted: an atomic load. Every writer keeps 0 <= current_level <= 100. The gate refuses this file under the
// concurrency row, which is the point. Verified code sees only the contract in example.cpp.
// The declaration in example.cpp carries the CPLUSP_TRUSTED marker.
std::atomic<int32_t> current_level{0};

int32_t level() {
  return current_level.load();
}
