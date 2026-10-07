#include <algorithm>
#include <array>
#include <cstddef>
#include <cstdint>
#include <cstdio>
#include "../../../../include/cplusp.h"

struct CPLUSP_PLAIN("an old record") Record {
  int count = 0;
  int extra = 0;
};

// A cast of a pointer to a plain object into another pointer type is a use, decision 0054. The type is gone, so no callee can be
// judged on what it gets.
uint8_t first_byte(const Record& r) {
  std::array<std::byte, 8> out{};
  std::copy_n(static_cast<const std::byte*>(static_cast<const void*>(&r)), 8, out.begin());
  return static_cast<uint8_t>(out[0]);
}

void dump_bytes(const void* p, std::size_t n, std::FILE* f) {
  std::fwrite(p, n, 1, f);
}

void dump(const Record& r, std::FILE* f) {
  dump_bytes(&r, sizeof r, f);
}
