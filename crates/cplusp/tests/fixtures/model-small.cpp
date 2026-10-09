#include <cstdint>

// Small forms: int8_t, int16_t and uint16_t, a right shift, a named constant, and a character in a contract, decision 0106.
constexpr int32_t kScale = 10;

//@ requires -0x80 <= x < 0x80
//@ ensures result == x
int8_t to_byte(int32_t x) {
  return static_cast<int8_t>(x);
}

//@ requires 0 <= x && x < 0x7FFF
//@ ensures result == x + 1
int16_t inc16(int16_t x) {
  return static_cast<int16_t>(x + 1);
}

//@ ensures result == x
uint16_t same16(uint16_t x) {
  return x;
}

//@ requires n < 32
//@ ensures result <= x
//@ ensures n == 0 ==> result == x
uint32_t shift(uint32_t x, uint32_t n) {
  return x >> n;
}

//@ requires -100 <= x && x < 0
//@ ensures x <= result && result < 0
int32_t shift_neg(int32_t x) {
  return x >> 1;
}

//@ requires -0x7FFFFF <= x && x <= 0x7FFFFF
//@ ensures result == x * kScale
int32_t scale(int32_t x) {
  return x * kScale;
}

//@ ensures result == ('0' <= c && c <= '9')
bool is_digit(uint8_t c) {
  return c >= '0' && c <= '9';
}

//@ requires x >= 0
//@ ensures result == x / 2
int32_t half(int32_t x) {
  return x >> 1;
}

//@ ensures result == -2
int32_t floor_neg() {
  int32_t x = -3;
  return x >> 1;
}

// Each constant reads as its true value in code and in a contract, decision 0107.
constexpr uint8_t kByte = 200;
constexpr uint16_t kHalf = 0xFFFF;
constexpr uint32_t kMask = 0xFFFFFFFF;
constexpr uint64_t kBig = 0xFFFFFFFFFFFFFFFF;
constexpr int8_t kLow8 = -128;
constexpr int64_t kLow64 = -9223372036854775807 - 1;

//@ ensures result == 200 && result == kByte
uint8_t byte_value() {
  return kByte;
}

//@ ensures result == 65535 && result == kHalf
uint16_t half_value() {
  return kHalf;
}

//@ ensures result == 4294967295 && result == kMask
uint32_t mask_value() {
  return kMask;
}

//@ ensures result == 18446744073709551615 && result == kBig
uint64_t big_value() {
  return kBig;
}

//@ ensures result == -128 && result == kLow8
int8_t low8_value() {
  return kLow8;
}

//@ ensures result == -9223372036854775808 && result == kLow64
int64_t low64_value() {
  return kLow64;
}
