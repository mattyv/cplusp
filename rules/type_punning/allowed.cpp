#include <array>
#include <bit>
#include <cstddef>
#include <cstdint>
#include <cstring>
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

// The std::byte of the system header holds no bad value, decision 0119.
std::array<std::byte, 4> as_bytes(uint32_t u) {
  return std::bit_cast<std::array<std::byte, 4>>(u);
}

// Bytes of a padded struct can go into a buffer of bytes.
struct Padded {
  uint8_t a;
  uint32_t b;
};

std::array<uint8_t, 8> raw(const Padded& p) {
  return std::bit_cast<std::array<uint8_t, 8>>(p);
}

// A raw copy into plain integer data makes a value, and a read through const bytes changes nothing, decision 0119.
CPLUSP_TRUSTED("copies bytes into two integers")
//@ ensures true
Two from_bytes(const std::array<uint8_t, 8>& b) {
  Two t{0, 0};
  std::memcpy(&t, &b, sizeof t);
  return t;
}

struct Flag {
  bool on;
};

CPLUSP_TRUSTED("reads the byte of a bool")
//@ ensures true
uint8_t flag_byte(const Flag& f) {
  return *reinterpret_cast<const uint8_t*>(&f.on);
}

// A template is judged at each instance. An instance that copies into plain integers is allowed, decision 0120.
//@ ensures true
template <class T>
CPLUSP_TRUSTED("loads a value from bytes")
T load(const uint8_t* p) {
  T t{};
  std::memcpy(&t, p, sizeof t);
  return t;
}

CPLUSP_TRUSTED("loads two integers")
//@ ensures true
Two load_two(const uint8_t* p) {
  return load<Two>(p);
}

// An empty base takes no bits, so it is no padding, decision 0120.
struct Empty {};
struct WithEmptyBase : Empty {
  uint32_t x;
};

uint32_t word(const WithEmptyBase& w) {
  return std::bit_cast<uint32_t>(w);
}
