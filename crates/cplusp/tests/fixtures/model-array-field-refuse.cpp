#include <array>
#include <cstdint>

// The forms of a std::array field that have no rule, decision 0196.
class NoStart {
 public:
  //@ ensures true
  explicit NoStart(int32_t k) : k_(k) {}

 private:
  std::array<int32_t, 4> items_;
  int32_t k_;
};
