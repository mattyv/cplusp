#include <cstdint>
#include <iostream>
#include <sstream>

void show(int32_t x) {
  std::cout << x;  // BANNED
}

void log(std::ostream& out, int32_t x) {  // BANNED
  out << x;
}

bool has_digits(int32_t x) {
  std::ostringstream s;  // BANNED
  s << x;
  return !s.str().empty();
}
