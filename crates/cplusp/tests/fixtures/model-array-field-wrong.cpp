#include <array>
#include <cstddef>
#include <cstdint>

// Claims about a std::array field that do not hold, decision 0196.
class Slots {
 public:
  //@ ensures items_[0] == 1
  Slots() : items_() {}

  // No requires line, so the index may be past the end.
  //@ ensures result == items_[i]
  int32_t at(size_t i) const { return items_[i]; }

  //@ requires i < 8
  //@ ensures items_[i] == x
  void put(size_t i, int32_t x) { items_[i + 1] = x; }

 private:
  std::array<int32_t, 8> items_;
};

//@ ensures result == 9
int32_t caller() {
  Slots s;
  s.put(3, 5);
  return s.at(3);
}
