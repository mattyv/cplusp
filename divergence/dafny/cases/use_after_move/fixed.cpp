#include <cstddef>
#include <cstdint>
#include <utility>
#include <vector>

//@ requires s.size() < 0x8000000000000000
//@ ensures result == 2 * old(s).size()
std::size_t total(std::vector<uint8_t> s) {
  std::vector<uint8_t> t = std::move(s);
  std::size_t n = t.size();
  return n + n;
}

// The witness calls this, and code.cpp has a function of the same name. The two bytes are "hi".
//@ ensures result == 4
std::size_t total_of_hi() {
  return total(std::vector<uint8_t>{0x68, 0x69});
}
