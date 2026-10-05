#include <cfloat>
#include <cmath>
#include <cstdint>

// A fixed-point number: an int64_t count of thousandths, so raw 12345 is 12.345. The hot path keeps its money, its prices and its
// times in this type and not in a double, for four reasons. The sum of two of them is exact, and the contract says it is an equality.
// A double cannot hold 0.001, so every sum rounds, and a contract for doubles is a bound, never an equality. The order of a sum changes
// a double result and never a fixed one. And an int64_t holds every integer up to 2^63 exactly, where a double stops at 2^53.
// The cost is the range, and each overflow is a precondition. The product of two raw values is a plain int64_t product, so it is
// checked before it is taken, and the division by 1000 truncates toward zero.
struct Fixed {
  int64_t raw;
};

//@ requires -0x8000000000000000 <= a.raw + b.raw <= 0x7FFFFFFFFFFFFFFF
//@ ensures result.raw == a.raw + b.raw
Fixed add(Fixed a, Fixed b) {
  return Fixed{a.raw + b.raw};
}

// The scaled product. The result is under one thousandth from the true product, and never larger than it in magnitude.
// ponytail: the raw product must fit in an int64_t, so both values are at most about 3 million in magnitude. The upgrade is to split
// one factor into a high and a low part, and to add the two scaled products.
//@ requires -0x8000000000000000 <= a.raw * b.raw <= 0x7FFFFFFFFFFFFFFF
//@ ensures result.raw == (a.raw * b.raw) / 1000
//@ ensures |1000 * result.raw| <= |a.raw * b.raw| && |a.raw * b.raw - 1000 * result.raw| < 1000
Fixed multiply(Fixed a, Fixed b) {
  return Fixed{(a.raw * b.raw) / 1000};
}

// The edge to a double, for a display or a trusted caller. The raw value converts exactly up to 2^53, and the division by 1000.0
// is the one rounding. Here eps is DBL_EPSILON / 2 and eta is DBL_TRUE_MIN / 2.
//@ requires -9007199254740992 <= f.raw <= 9007199254740992
//@ ensures |result - f.raw / 1000.0| <= eps * |f.raw / 1000.0| + eta
double to_double(Fixed f) {
  double whole = static_cast<double>(f.raw);
  return whole / 1000.0;
}

// A verified caller: a price with a tax of 250 thousandths, a quarter. The product comes first and then the sum, and the contracts of
// both calls give the proof that neither overflows.
//@ requires -1000000000000000 <= price.raw <= 1000000000000000
//@ ensures result.raw == price.raw + (price.raw * 250) / 1000
Fixed price_with_tax(Fixed price) {
  Fixed tax = multiply(price, Fixed{250});
  return add(price, tax);
}
