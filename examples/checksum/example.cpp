#include <cstddef>
#include <cstdint>
#include <span>

// A checksum: the sum of the bytes in a span, modulo 256. The accumulator is a uint32_t, and each step reduces it, so it stays below 256
// and nothing wraps. The trap is integral promotion. A uint8_t operand becomes an int before the addition, so `sum + bytes[i]` is an int
// sum, and it is not reduced modulo 256 until the store. The usual code is `uint8_t sum = 0; sum += bytes[i];`, and the same code
// written `sum = sum + bytes[i];` is the other. Both hide the narrowing in the store. The gate refuses each, at that line: "Implicit
// narrowing conversion: not allowed in verified code. The value changes with no sign in the source. C++20 wraps an integer, and a
// double loses its fraction. Use a static_cast with a contract that the value fits, or a wider type." Here the width is a choice in
// the source, and the one cast at the end fits by the invariant. Sum is the specification function, and example.dfy defines it as the
// sum of the bytes with no modulus.
//@ ensures result == Sum(bytes) % 256
uint8_t checksum(std::span<const uint8_t> bytes) {
  uint32_t acc = 0;
  //@ invariant 0 <= i <= bytes.size()
  //@ invariant acc == Sum(bytes[..i]) % 256
  for (size_t i = 0; i < bytes.size(); ++i) {
    acc = (acc + bytes[i]) % 256;
  }
  return static_cast<uint8_t>(acc);
}

// A verified caller: does the data match the checksum that came with it.
//@ ensures result == (Sum(bytes) % 256 == expected)
bool matches(std::span<const uint8_t> bytes, uint8_t expected) {
  return checksum(bytes) == expected;
}
