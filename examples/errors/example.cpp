#include <cstdint>

// An error as a value. The choice a C++ programmer makes first is std::expected, and it does not compile under the pinned toolchain.
// Clang 18 with libstdc++ 13 leaves the header <expected> empty, so the gate says, for a function that returns
// `std::expected<int32_t, Error>` and one that calls `std::unexpected(Error::Negative)`:
// "does not compile: <file>:<line>: no template named 'expected' in namespace 'std'" and
// "does not compile: <file>:<line>: no member named 'unexpected' in namespace 'std'".
// A throw is the other first choice, and the gate refuses it at that line: "Exceptions: not allowed in verified code. Verified code is
// noexcept. Use std::expected." That advice cannot be followed today. The shape that works is a struct with a flag, an error and a value.
// The error is an enum class, and the value is 0 when there is an error. The caller handles each error in a switch over all of them.
// A square above 46340 does not fit in int32_t, and the function says so as an error and does not overflow.
enum class Error : uint8_t { None, Negative, TooBig };

struct Result {
  bool ok;
  Error error;
  int32_t value;
};

//@ ensures result.ok == (result.error == Error::None)
//@ ensures x < 0 ==> !result.ok && result.error == Error::Negative && result.value == 0
//@ ensures x > 46340 ==> !result.ok && result.error == Error::TooBig && result.value == 0
//@ ensures 0 <= x && x <= 46340 ==> result.ok && result.value == x * x
Result checked_square(int32_t x) {
  if (x < 0) {
    return Result{false, Error::Negative, 0};
  }
  if (x > 46340) {
    return Result{false, Error::TooBig, 0};
  }
  return Result{true, Error::None, x * x};
}

// A caller that handles both errors, and the value. Each error has its own code, and the code is below zero.
//@ ensures x < 0 ==> result == -1
//@ ensures x > 46340 ==> result == -2
//@ ensures 0 <= x && x <= 46340 ==> result == x * x
int32_t square_or_code(int32_t x) {
  Result r = checked_square(x);
  switch (r.error) {
    case Error::None:
      return r.value;
    case Error::Negative:
      return -1;
    case Error::TooBig:
      return -2;
  }
  // No other value arrives here, because the enum_cast row keeps a value that is no enumerator out. The compiler needs this return.
  return r.value;
}
