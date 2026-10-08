#include <cstdint>
#include <span>
#include <vector>

// A sequence passes to a sequence parameter with its value, decision 0070.
//@ requires v.size() > 0
//@ ensures result == v[0]
int32_t first_span(std::span<const int32_t> v) {
  return v[0];
}

//@ requires values.size() > 0
//@ ensures result == values[0]
int32_t via_span(std::span<const int32_t> values) {
  return first_span(values);
}

//@ requires values.size() > 0
//@ ensures result == values[0]
int32_t via_vector(const std::vector<int32_t>& values) {
  return first_span(values);
}

//@ ensures result == v[0]
int32_t via_fixed(std::span<const int32_t, 3> v) {
  return first_span(v);
}
