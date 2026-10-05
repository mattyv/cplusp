#include <cstddef>
#include <string>

//@ ensures result == position of 'z' in s, plus one
std::size_t after(const std::string& s) {
  return s.find('z') + 1;
}

std::size_t after_z() {
  return after("abc");
}
