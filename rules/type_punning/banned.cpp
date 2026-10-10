#include <array>
#include <bit>
#include <cstdint>
#include <cstring>
#include <experimental/simd>
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

// A bit cast to a type that holds an enum or a bool can make a value that is not one, decision 0118.
enum class Kind : uint8_t { Small, Large };

struct Boxed {
  Kind k;
};

struct Flagged {
  bool on;
};

CPLUSP_TRUSTED("makes a boxed kind from a byte")
//@ ensures true
Boxed boxed(uint8_t b) {
  return std::bit_cast<Boxed>(b);  // BANNED
}

CPLUSP_TRUSTED("makes a bool from a byte")
//@ ensures true
bool flag(uint8_t b) {
  return std::bit_cast<bool>(b);  // BANNED
}

CPLUSP_TRUSTED("makes a flagged struct from a byte")
//@ ensures true
Flagged flagged(uint8_t b) {
  return std::bit_cast<Flagged>(b);  // BANNED
}

// An array of pointers holds pointers.
CPLUSP_TRUSTED("makes pointers from a number")
//@ ensures true
int32_t via_array(uint64_t bits) {
  return *std::bit_cast<std::array<const int32_t*, 1>>(bits)[0];  // BANNED also: raw_pointer
}

// The library makes the same bit cast as std::bit_cast, decision 0119.
CPLUSP_TRUSTED("reads a double through a span made by a bit cast of the library")
//@ ensures true
int32_t lib_span(const double& d) {
  return std::experimental::__bit_cast<std::span<const int32_t, 1>>(&d)[0];  // BANNED
}

CPLUSP_TRUSTED("makes a bool from a byte with the library")
//@ ensures true
bool lib_flag(uint8_t b) {
  return std::experimental::__bit_cast<bool>(b);  // BANNED
}

// The padding of the source has no value, [bit.cast] paragraph 2, decision 0119.
struct Padded {
  uint8_t a;
  uint32_t b;
};

CPLUSP_TRUSTED("packs a padded struct")
//@ ensures true
uint64_t packed(const Padded& p) {
  return std::bit_cast<uint64_t>(p);  // BANNED
}

// A raw copy into a bool, an enum or a pointer makes a bad value, decision 0119.
CPLUSP_TRUSTED("copies a byte into a bool")
//@ ensures true
bool copy_flag(uint8_t b) {
  Flagged f{false};
  std::memcpy(&f, &b, 1);  // BANNED
  return f.on;
}

CPLUSP_TRUSTED("clears a boxed kind")
//@ ensures true
Boxed clear_boxed() {
  Boxed x{Kind::Small};
  std::memset(&x, 7, sizeof x);  // BANNED
  return x;
}

CPLUSP_TRUSTED("copies a number into a span")
//@ ensures true
int32_t copy_span(std::span<const int32_t> s, uint64_t bits) {
  std::memmove(&s, &bits, sizeof bits);  // BANNED
  return s[0];
}

// A write through a pointer to bytes that is not const, decision 0119.
CPLUSP_TRUSTED("writes a byte into a bool")
//@ ensures true
bool write_flag(uint8_t b) {
  Flagged f{false};
  *reinterpret_cast<uint8_t*>(&f.on) = b;  // BANNED
  return f.on;
}

// The gate cannot know the type behind void*, so the row fails closed, decision 0119.
CPLUSP_TRUSTED("copies bytes to an unknown place")
//@ ensures true
void copy_unknown(void* dst, const uint8_t& b) {
  std::memcpy(dst, &b, 1);  // BANNED
}
