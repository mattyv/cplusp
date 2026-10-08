// A companion file from the second review of the companion check, decision 0083.
#include <cstdint>
#include <optional>
//@ ensures !result.has_value()
std::optional<int32_t> f(int32_t a) { return a; }
