#include <bit>
#include <cstdint>
#include "../../include/cplusp.h"

struct A {
  int32_t x;
};

struct B {
  int32_t y;
};

// Each read is through a type that C++ does not allow for the object, [basic.lval] and [expr.ref]. The row holds in trusted code.
CPLUSP_TRUSTED("reads half a word")
//@ ensures true
uint16_t half(const uint32_t& w) {
  return *reinterpret_cast<const uint16_t*>(&w);  // BANNED
}

CPLUSP_TRUSTED("reads half a word by reference")
//@ ensures true
uint16_t half_ref(const uint32_t& w) {
  return reinterpret_cast<const uint16_t&>(w);  // BANNED
}

CPLUSP_TRUSTED("reads half a word through void")
//@ ensures true
uint16_t half_void(const uint32_t& w) {
  return *static_cast<const uint16_t*>(static_cast<const void*>(&w));  // BANNED
}

CPLUSP_TRUSTED("reads one struct as another")
//@ ensures true
int32_t other(const A& a) {
  return reinterpret_cast<const B*>(&a)->y;  // BANNED
}

CPLUSP_TRUSTED("reads a word as its signed type")
//@ ensures true
int32_t as_signed(const uint32_t& w) {
  return *reinterpret_cast<const int32_t*>(&w);  // BANNED
}

// std::bit_cast to a pointer makes the same pointer with no cast.
CPLUSP_TRUSTED("reads half a word through a bit cast pointer")
//@ ensures true
uint16_t half_bits(const uint32_t& w) {
  return *std::bit_cast<const uint16_t*>(&w);  // BANNED
}
