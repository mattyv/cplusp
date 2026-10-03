#include <cstdint>

struct Flags {
  uint32_t bits = 0;
};

constexpr uint32_t kReadable = 1;
constexpr uint32_t kWritable = 2;

bool can_write(const Flags& f) {
  return (f.bits & kWritable) != 0;
}

Flags make_readable() {
  return Flags{kReadable};
}
