#include <any>
#include <bitset>
#include <cstddef>
#include <cstdint>
#include <memory>
#include <ranges>
#include <vector>

void view(const std::unique_ptr<std::ranges::ref_view<std::vector<int32_t>>>& p) {
  auto rv = *p;
  rv[0] = 1;
}

void bits(const std::unique_ptr<std::vector<bool>>& p) {
  auto r = (*p)[0];
  r = true;
}

void bitset_ref(const std::unique_ptr<std::bitset<8>>& p) {
  auto r = (*p)[0];
  r = true;
}

void any_copy(const std::unique_ptr<std::any>& p) {
  auto a = *p;
  *std::any_cast<int32_t*>(a) = 1;
}

//@ requires p != nullptr
//@ ensures result == p->size()
std::size_t copy_owner(const std::unique_ptr<std::vector<int32_t>>& p) {
  std::vector<int32_t> c = *p;
  return c.size();
}
