#include <cstdint>
#include "../../../../include/cplusp.h"

// A std::byte that the file declares itself is no view as bytes. Only the one of the system header is, decision 0117.
namespace std {
enum class byte : uint32_t {};
}

CPLUSP_TRUSTED("reads a double as its own byte")
//@ ensures true
uint32_t first(const double& d) {
  return static_cast<uint32_t>(*reinterpret_cast<const std::byte*>(&d));
}
