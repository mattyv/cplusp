#include <cstddef>
#include <string>

//@ ensures result == (s has 'z' ? its position + 1 : 0)
std::size_t after(const std::string& s) {
  const std::size_t p = s.find('z');
  return p == std::string::npos ? 0 : p + 1;
}
