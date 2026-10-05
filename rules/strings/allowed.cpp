#include <cstddef>
#include <cstdint>
#include <span>

// Text in verified code is bytes. A span of them, with the contract on the bytes.
//@ requires prefix.size() <= text.size()
//@ ensures result == (forall i :: 0 <= i < prefix.size() ==> text[i] == prefix[i])
bool starts_with(std::span<const uint8_t> text, std::span<const uint8_t> prefix) {
  for (size_t i = 0; i < prefix.size(); ++i) {
    if (text[i] != prefix[i]) {
      return false;
    }
  }
  return true;
}
