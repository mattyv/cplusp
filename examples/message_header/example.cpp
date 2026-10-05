#include <cstddef>
#include <cstdint>
#include <optional>
#include <span>

// A header of four bytes in a span: a version byte, a length in two bytes with the low byte first, and a kind byte. A span shorter
// than four bytes has no header, and the answer is an empty optional. The contract names the bytes: the length is byte 1 plus 256 times
// byte 2, which is what little-endian means. The code says the same sum. The shift form, `(bytes[2] << 8) | bytes[1]`, is the same number.
// Dafny does not prove that equality in the 32 bits that int has after promotion, and it times out, so the sum is the form to write.
// The sum is in int, because the bytes promote, and it is at most 65535, so the cast to uint16_t loses nothing. The field is named
// kind and not type, because type is a keyword in Dafny.
struct Header {
  uint8_t version;
  uint16_t length;
  uint8_t kind;
};

//@ ensures result.has_value() == (bytes.size() >= 4)
//@ ensures result.has_value() ==> result->version == bytes[0] && result->kind == bytes[3]
//@ ensures result.has_value() ==> result->length == bytes[1] + 256 * bytes[2]
std::optional<Header> parse_header(std::span<const uint8_t> bytes) {
  if (bytes.size() < 4) {
    return std::nullopt;
  }
  return Header{bytes[0], static_cast<uint16_t>(bytes[1] + 256 * bytes[2]), bytes[3]};
}

// A verified caller. The whole frame is the header and then the number of bytes the length says. The caller proves its answer from the
// contract of parse_header, and it reads no byte of a span that is too short.
//@ ensures result == (bytes.size() >= 4 && bytes.size() - 4 >= bytes[1] + 256 * bytes[2])
bool frame_complete(std::span<const uint8_t> bytes) {
  std::optional<Header> h = parse_header(bytes);
  if (!h.has_value()) {
    return false;
  }
  return bytes.size() - 4 >= static_cast<size_t>(h->length);
}
