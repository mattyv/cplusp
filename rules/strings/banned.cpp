#include <cstddef>
#include <cstdint>
#include <string>
#include <string_view>

size_t length_of(const std::string& s) {  // BANNED
  return s.size();
}

bool empty_view(std::string_view v) {  // BANNED
  return v.empty();
}

size_t three() {
  std::string s = "abc";  // BANNED
  return s.size();
}
