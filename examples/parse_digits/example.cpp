#include <cstddef>
#include <cstdint>
#include <optional>
#include <span>

// Digits in a span become a number, or nothing when a byte is no digit or the span is empty. Value is the specification function,
// and example.dfy defines it as the fold of 10 * acc + digit. At most nine digits fit in an int32_t. The loop invariant keeps the
// running value below 10 to the power of the digits read, so each step stays in range.
//@ requires digits.size() <= 9
//@ ensures result.has_value() == (digits.size() > 0 && forall i :: 0 <= i < digits.size() ==> '0' <= digits[i] <= '9')
//@ ensures result.has_value() ==> result.value() == Value(digits)
std::optional<int32_t> parse_digits(std::span<const uint8_t> digits) {
  if (digits.empty()) {
    return std::nullopt;
  }
  int32_t acc = 0;
  //@ invariant 0 <= i <= digits.size()
  //@ invariant forall j :: 0 <= j < i ==> '0' <= digits[j] <= '9'
  //@ invariant acc == Value(digits[..i])
  for (size_t i = 0; i < digits.size(); ++i) {
    uint8_t d = digits[i];
    if (d < '0' || d > '9') {
      return std::nullopt;
    }
    //@ apply ValueBound(digits[..i])
    //@ apply Pow10AtMost(i, 8)
    //@ assert Pow10(8) == 100000000
    //@ assert digits[..i + 1][..i] == digits[..i]
    acc = acc * 10 + (d - '0');
  }
  //@ assert digits[..digits.size()] == digits
  return acc;
}
