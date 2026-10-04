#include <cstdint>

// Volatile is for hardware access, so the accessor is trusted, and its contract says what every read keeps, a range. The body
// is in trusted.cpp. Two reads may differ, and the caller reads once.
//@ ensures result <= 255
uint32_t read_status();

//@ ensures result <= 255
uint32_t headroom() {
  uint32_t s = read_status();
  return 255 - s;
}
