#include <array>
#include <cstddef>
#include <cstdint>
#include <span>
#include "../../include/cplusp.h"

// Text in the subset is a span of bytes. The type char is banned, and a function with a char in it is refused at that line: "Plain `int`,
// `long`, `short`, `char` and the other built-in integer types: not allowed in verified code. The compiler sets the width and the
// signedness of these types. The source does not say them, and the proof needs them. Use int32_t, uint8_t and the other fixed-width
// types from <cstdint>, bool, and size_t for sizes." A uint8_t has a width and no sign trouble, so a contract can name each byte.
// A std::string parameter is refused as well, under the row `strings`, decision 0031. For `bool is_empty(const std::string& s)` the gate
// prints at the line of the parameter: "`std::string`, `std::string_view`: allowed only in trusted code. Text is a sequence of `char`,
// whose signedness the compiler sets, and the model has no text type. Verified code reads text as bytes. Use std::span<const uint8_t>,
// or mark the function trusted with a reason." A contract on the bytes is the shape that has a meaning for the prover. A byte string is
// not a text in any encoding. It is the bytes a text is made of.
//@ ensures result == (text.size() >= prefix.size() && forall i :: 0 <= i < prefix.size() ==> text[i] == prefix[i])
bool starts_with(std::span<const uint8_t> text, std::span<const uint8_t> prefix) {
  if (prefix.size() > text.size()) {
    return false;
  }
  //@ invariant 0 <= i <= prefix.size()
  //@ invariant forall j :: 0 <= j < i ==> text[j] == prefix[j]
  for (size_t i = 0; i < prefix.size(); ++i) {
    if (text[i] != prefix[i]) {
      return false;
    }
  }
  return true;
}

// A verified caller. The prefix is the four bytes of "GET ", written in hex, and the contract names each of them.
//@ ensures result == (line.size() >= 4 && line[0] == 0x47 && line[1] == 0x45 && line[2] == 0x54 && line[3] == 0x20)
bool is_get_request(std::span<const uint8_t> line) {
  const std::array<uint8_t, 4> get = {0x47, 0x45, 0x54, 0x20};
  return starts_with(line, get);
}

// The one place for a std::string is a trusted function. This one calls std::to_string, which writes the digits of a number. The body is
// in trusted.cpp, and the gate refuses it under the row `strings`. A verified caller sees only the contract. An int32_t has at most ten
// digits and a sign, and the contract says how many bytes the function writes: one below ten, two below a hundred, eleven at most.
CPLUSP_TRUSTED("std::to_string writes the digits of n, and an int32_t has at most ten digits and a sign")
//@ ensures 1 <= result && result <= 11
//@ ensures 0 <= n && n < 10 ==> result == 1
//@ ensures 10 <= n && n < 100 ==> result == 2
size_t decimal_width(int32_t n);

// A verified caller. The width of "row,column" is the two numbers and the comma. It is three bytes when both are one digit.
//@ ensures 3 <= result && result <= 23
//@ ensures 0 <= row && row < 10 && 0 <= col && col < 10 ==> result == 3
size_t position_width(int32_t row, int32_t col) {
  const size_t row_width = decimal_width(row);
  return row_width + 1 + decimal_width(col);
}
