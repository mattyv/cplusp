#include <array>
#include <cstddef>
#include <cstdint>
#include <optional>
#include <span>

// The search is over bytes, and its result says in its type that there may be no match. There is no npos, so no arithmetic on one.
//@ ensures result.has_value() ==> *result < text.size() && text[*result] == c
//@ ensures !result.has_value() ==> forall i :: 0 <= i < text.size() ==> text[i] != c
std::optional<size_t> find_byte(std::span<const uint8_t> text, uint8_t c) {
  //@ invariant 0 <= i <= text.size()
  //@ invariant forall j :: 0 <= j < i ==> text[j] != c
  for (size_t i = 0; i < text.size(); ++i) {
    if (text[i] == c) {
      return i;
    }
  }
  return std::nullopt;
}

//@ ensures result == (find_byte(text, 'z').has_value() ? *find_byte(text, 'z') + 1 : 0)
size_t after(std::span<const uint8_t> text) {
  const std::optional<size_t> p = find_byte(text, 'z');
  if (!p.has_value()) {
    return 0;
  }
  return *p + 1;
}

// The witness calls this, and code.cpp has a function of the same name. The text is the three bytes of "abc", and it has no 'z'.
//@ ensures result == 0
size_t after_z() {
  const std::array<uint8_t, 3> abc = {'a', 'b', 'c'};
  return after(abc);
}
