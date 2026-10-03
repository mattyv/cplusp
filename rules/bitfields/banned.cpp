#include <cstdint>
struct Flags {
  uint32_t readable : 1 = 0;  // BANNED
  uint32_t writable : 1 = 0;  // BANNED
  uint32_t reserved : 6 = 0;  // BANNED
};

bool can_write(const Flags& f) {
  return f.writable != 0;
}
