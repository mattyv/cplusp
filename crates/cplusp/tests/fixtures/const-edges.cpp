#include <cstdint>
#include <memory>

namespace std {
struct deque {
  int32_t n = 0;
  int32_t& at(int32_t) {
    n += 1;
    return n;
  }
};
}  // namespace std

int32_t first(const std::unique_ptr<std::deque>& p) {
  return p->at(0) + 1;
}

struct Opaque;

//@ ensures true
void take_opaque(const Opaque& o);

void hand_over(const std::unique_ptr<Opaque>& p) {
  take_opaque(*p);
}
