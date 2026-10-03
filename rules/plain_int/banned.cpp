#include <array>
#include <cstdint>

int twice(int x) {  // BANNED
  return 2 * x;
}

int32_t narrow(int64_t x) {
  return static_cast<int>(x);  // BANNED
}

uint32_t first(const std::array<unsigned, 4>& table) {  // BANNED
  return table[0];
}

bool is_a(char letter) {  // BANNED
  return letter == 'a';
}

int64_t widen(int32_t x) {
  long long wide = x;  // BANNED
  return wide;
}
