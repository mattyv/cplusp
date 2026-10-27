#include <cstddef>
#include <cstdint>
#include <utility>
#include <vector>

// The forms of a vector by value that have no rule, decision 0194.
class Probe {
 public:
  //@ ensures result == (v.size() > 0)
  bool any(std::vector<int32_t> v) const { return v.size() > 0; }

  //@ requires any(v)
  //@ ensures true
  int32_t first(std::vector<int32_t> v) const { return v.at(0); }
};

//@ ensures true
size_t flags(std::vector<bool> v) {
  return v.size();
}
