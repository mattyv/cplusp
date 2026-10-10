#include <array>
#include <bit>
#include <cstddef>
#include <cstdint>
#include <cstring>
#include <experimental/simd>
#include <memory>
#include <span>
#include <strings.h>
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

// A pointer from an integer, a cast that takes const away, and the library view of bytes reach the same bool, decision 0120.
CPLUSP_TRUSTED("writes a byte into a bool through an integer")
//@ ensures true
bool write_by_address(uint8_t b) {
  Flagged f{false};
  *reinterpret_cast<uint8_t*>(std::bit_cast<uintptr_t>(&f.on)) = b;  // BANNED
  return f.on;
}

CPLUSP_TRUSTED("writes a byte into a bool through a const_cast")
//@ ensures true
bool write_unconst(uint8_t b) {
  Flagged f{false};
  *const_cast<uint8_t*>(reinterpret_cast<const uint8_t*>(&f.on)) = b;  // BANNED
  return f.on;
}

CPLUSP_TRUSTED("writes a byte into a bool through as_writable_bytes")
//@ ensures true
bool write_view(uint8_t b) {
  Flagged f{false};
  std::as_writable_bytes(std::span<bool, 1>(&f.on, 1))[0] = static_cast<std::byte>(b);  // BANNED
  return f.on;
}

// More functions of the C library copy raw bytes, decision 0120.
CPLUSP_TRUSTED("bcopy into a bool")
//@ ensures true
bool bcopy_flag(uint8_t b) {
  Flagged f{false};
  bcopy(&b, &f, 1);  // BANNED
  return f.on;
}

CPLUSP_TRUSTED("bzero of a bool")
//@ ensures true
bool bzero_flag() {
  Flagged f{true};
  bzero(&f, 1);  // BANNED
  return f.on;
}

CPLUSP_TRUSTED("mempcpy into a bool")
//@ ensures true
bool mempcpy_flag(uint8_t b) {
  Flagged f{false};
  static_cast<void>(mempcpy(&f, &b, 1));  // BANNED
  return f.on;
}

CPLUSP_TRUSTED("memccpy into a bool")
//@ ensures true
bool memccpy_flag(uint8_t b) {
  Flagged f{false};
  static_cast<void>(memccpy(&f, &b, 0, 1));  // BANNED
  return f.on;
}

// The gate cannot follow a pointer to a copy function, so the row fails closed at the name, decision 0120.
CPLUSP_TRUSTED("memcpy through a pointer into a bool")
//@ ensures true
bool copy_by_pointer(uint8_t b) {
  Flagged f{false};
  auto copy = std::memcpy;  // BANNED
  static_cast<void>(copy(&f, &b, 1));
  return f.on;
}

// A class with virtual functions holds a hidden pointer, decision 0120.
struct Shape {
  virtual ~Shape() = default;
  virtual int32_t area() const { return side; }
  int32_t side = 0;
};

CPLUSP_TRUSTED("copies bytes into a polymorphic object")
//@ ensures true
int32_t copy_shape(const uint8_t* src) {
  Shape s{};
  std::memcpy(&s, src, sizeof s);  // BANNED
  return s.area();
}

// The gate cannot know the fields of an incomplete type, so the row fails closed, decision 0120.
struct Fwd;
struct Two {
  int32_t a;
  int32_t b;
};

CPLUSP_TRUSTED("copies bytes into an incomplete type")
//@ ensures true
void copy_to_fwd(Fwd* dst, const uint8_t* src) {
  std::memcpy(dst, src, 4);  // BANNED
}

CPLUSP_TRUSTED("copies an incomplete type into two integers")
//@ ensures true
Two copy_from_fwd(const Fwd* src) {
  Two t{0, 0};
  std::memcpy(&t, src, sizeof t);  // BANNED
  return t;
}

// The row judges each instance of a template, decision 0120.
//@ ensures true
template <class T>
CPLUSP_TRUSTED("loads a value from bytes")
T load(const uint8_t* p) {
  T t{};
  std::memcpy(&t, p, sizeof t);  // BANNED
  return t;
}

CPLUSP_TRUSTED("loads a bool from bytes")
//@ ensures true
Flagged load_flag(const uint8_t* p) {
  return load<Flagged>(p);
}

// A functional cast can take const away too, and a write through bytes can reach an incomplete type, decision 0120.
using BytePointer = uint8_t*;

CPLUSP_TRUSTED("writes a byte into a bool through a functional cast")
//@ ensures true
bool write_functional(uint8_t b) {
  Flagged f{false};
  *BytePointer(reinterpret_cast<const uint8_t*>(&f.on)) = b;  // BANNED
  return f.on;
}

CPLUSP_TRUSTED("writes a byte into an incomplete type")
//@ ensures true
void write_fwd(Fwd* q, uint8_t b) {
  *reinterpret_cast<uint8_t*>(q) = b;  // BANNED
}
