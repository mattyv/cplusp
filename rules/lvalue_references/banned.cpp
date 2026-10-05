#include <cstdint>
#include <vector>

class Holder {
 public:
  explicit Holder(int32_t& target) : target_(target) {}

 private:
  int32_t& target_;  // BANNED
};

int32_t alias(int32_t x) {
  int32_t& r = x;  // BANNED
  r = 5;
  return x;
}

int32_t through_const_alias(const std::vector<int32_t>& v) {
  const std::vector<int32_t>& w = v;  // BANNED
  return w.empty() ? 0 : w.front();
}
