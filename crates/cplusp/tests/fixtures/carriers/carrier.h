#pragma once
#include <cstdint>
#include <span>

// A type of a library that carries a way to write: a pointer member, a span member, and const methods that hand them out.
struct Carrier {
  int32_t* raw;
  std::span<int32_t> sp;
  int32_t* get() const { return raw; }
  int32_t& ref() const { return *raw; }
  std::span<int32_t> view() const { return sp; }
};
