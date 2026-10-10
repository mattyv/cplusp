#include <array>
#include <bit>
#include <cstddef>
#include <cstdint>
#include "../../include/cplusp.h"

// Any object can be read as bytes, also in trusted code. uint8_t is unsigned char.
CPLUSP_TRUSTED("reads the first byte of a word")
//@ ensures true
uint8_t first_byte(const uint32_t& w) {
  return *reinterpret_cast<const uint8_t*>(&w);
}

CPLUSP_TRUSTED("reads the first byte of a word as std::byte")
//@ ensures true
std::byte first_raw(const uint32_t& w) {
  return *reinterpret_cast<const std::byte*>(&w);
}

// std::bit_cast gives the bits of a value with no pointer.
uint16_t low_half(uint32_t w) {
  return static_cast<uint16_t>(std::bit_cast<uint32_t>(w) & 0xFFFF);
}

// A cast that only adds const changes no type.
int32_t first(const int32_t* p) {
  return *static_cast<const int32_t*>(p);
}

// A bit cast between types that hold only integers is defined, because each bit pattern is a value, decision 0118.
struct Two {
  int32_t a;
  int32_t b;
};

int32_t second(const Two& t) {
  return std::bit_cast<std::array<int32_t, 2>>(t)[1];
}

uint64_t packed(const Two& t) {
  return std::bit_cast<uint64_t>(t);
}

// A bit cast of a pointer to an integer makes no pointer.
CPLUSP_TRUSTED("reads the address of a word")
//@ ensures true
uintptr_t address(const uint32_t& w) {
  return std::bit_cast<uintptr_t>(&w);
}
