#include <cstdint>
#include <functional>
#include <tuple>
#include <utility>
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

void take(int32_t& dst, int32_t& src);
int32_t set_and_read(int32_t& a, const int32_t& b);

// A reference wrapper is a reference local in disguise.
int32_t through_wrapper(int32_t x) {
  std::reference_wrapper<int32_t> r = std::ref(x);  // BANNED also: containers
  r.get() = 5;
  return x;
}

// So is a wrapper made for one call.
int32_t wrapped_argument(int32_t x) {
  return set_and_read(x, std::cref(x));  // BANNED
}

// A tuple or a pair of references holds two reference locals.
void tied(int32_t x, int32_t y) {
  auto [a, b] = std::tie(x, y);  // BANNED
  take(a, b);
}

void paired(int32_t x, int32_t y) {
  std::pair<int32_t&, int32_t&> pr(x, y);  // BANNED
  take(pr.first, pr.second);
}

void tied_whole(int32_t x, int32_t y) {
  auto t = std::tie(x, y);  // BANNED
  take(std::get<0>(t), y);
}
