#include <cstddef>
#include <string>
#include <utility>

//@ requires s.size() < 0x8000000000000000
//@ ensures result == 2 * old(s).size()
std::size_t total(std::string s) {
  std::string t = std::move(s);
  std::size_t n = t.size();
  return n + n;
}
