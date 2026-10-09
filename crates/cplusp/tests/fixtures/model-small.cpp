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
