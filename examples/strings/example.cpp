#include <array>
#include <cstddef>
#include <cstdint>
#include <span>

// Text in the subset is a span of bytes. The type char is banned, and a function with a char in it is refused at that line: "Plain `int`,
// `long`, `short`, `char` and the other built-in integer types: not allowed in verified code. The compiler sets the width and the
// signedness of these types. The source does not say them, and the proof needs them. Use int32_t, uint8_t and the other fixed-width
// types from <cstdint>, bool, and size_t for sizes." A uint8_t has a width and no sign trouble, so a contract can name each byte.
// The gate does not refuse a std::string parameter. For `bool f(const std::string& s)`, and for a body that reads `s[0] == 'a'`, it
// prints "ok: no findings". The matchers read the types that the source writes, and the char is inside the library type. So the ban on
// char does not reach text held in a std::string, and this example does not rely on the gate for that. A contract on the bytes is the
// shape that has a meaning for the prover. A byte string is not a text in any encoding. It is the bytes a text is made of.
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
