#include <bit>
#include <cstdint>
#include <memory>
#include <span>
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

// A round trip through an integer makes the same pointer, decision 0117.
CPLUSP_TRUSTED("reads a double through an integer")
//@ ensures true
int32_t via_integer(const double& d) {
  return *reinterpret_cast<const int32_t*>(std::bit_cast<uintptr_t>(&d));  // BANNED
}

// std::bit_cast to a class that holds a pointer makes the pun with no cast, decision 0117.
CPLUSP_TRUSTED("reads a double through a span")
//@ ensures true
int32_t via_span(const double& d) {
  return std::bit_cast<std::span<const int32_t, 1>>(&d)[0];  // BANNED
}

// The casts of std::shared_ptr cast inside the library, decision 0117.
CPLUSP_TRUSTED("reads a double through a shared pointer")
//@ ensures true
int32_t via_shared(double d) {
  return *std::reinterpret_pointer_cast<int32_t>(std::make_shared<double>(d));  // BANNED
}

CPLUSP_TRUSTED("reads a double through a shared pointer to void")
//@ ensures true
int32_t via_shared_void(double d) {
  return *std::static_pointer_cast<int32_t>(std::shared_ptr<void>(std::make_shared<double>(d)));  // BANNED
}

// A call through a pointer to a function of another type has undefined behaviour, decision 0117.
int32_t twice(int32_t x) {
  return x * 2;
}

CPLUSP_TRUSTED("calls a function as another type")
//@ ensures true
int64_t call_other(int64_t x) {
  return reinterpret_cast<int64_t (*)(int64_t)>(&twice)(x);  // BANNED
}
