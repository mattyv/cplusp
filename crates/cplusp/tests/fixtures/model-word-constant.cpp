#include <cstdint>

// A constant of the file with the name of a contract word is refused where a contract reads the word, decision 0158. The value
// of eps has no form in the model, and the check still sees its name.
constexpr double eps = 0x1p64;
constexpr int32_t eta = 1;

//@ ensures result > eps
double above() {
  return 1.0;
}

//@ ensures result > eta
double above_eta() {
  return 1.0;
}
