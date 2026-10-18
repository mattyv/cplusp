#include <cstddef>
#include <cstdint>
#include <span>
#include <vector>

// When a team bans variable_index, a variable index into a vector, a span or with at() is a finding, as one into an array is.
int32_t from_vector(const std::vector<int32_t>& v, size_t i) {
  return v[i];
}

int32_t from_span(std::span<const int32_t> s, size_t i) {
  return s[i];
}

int32_t with_at(const std::vector<int32_t>& v, size_t i) {
  return v.at(i);
}

int32_t constant_index(const std::vector<int32_t>& v) {
  return v[0] + v.at(1);
}
