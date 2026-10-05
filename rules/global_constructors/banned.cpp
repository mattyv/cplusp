#include <cstdint>
#include <string>

int32_t five();

int32_t base_value = five();  // BANNED

std::string name = "cplusp";  // BANNED also: strings

int32_t five() {
  return 5;
}
