#include <cstdint>
#include <span>
#include <vector>

// Sequences with no rule are refused at their lines, decision 0064.
int32_t mutable_ref(std::vector<int32_t>& v) {
  return 0;
}

int32_t mutable_span(std::span<int32_t> s) {
  return 0;
}

bool bools(const std::vector<bool>& v) {
  return true;
}

int32_t local_seq(const std::vector<int32_t>& v) {
  std::span<const int32_t> s = v;
  return 0;
}

int32_t at(const std::vector<int32_t>& v) {
  return v.at(0);
}

std::span<const int32_t> give_back(std::span<const int32_t> s) {
  return s;
}

//@ ensures result == x[0]
int32_t not_seq(int32_t x) {
  return x;
}

//@ ensures 0 < x > 1
int32_t mixed(int32_t x) {
  return x;
}
