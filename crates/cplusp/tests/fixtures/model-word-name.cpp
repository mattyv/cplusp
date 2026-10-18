#include <cstdint>

// A parameter and a field with the name of a contract word are refused where a contract reads the word, decision 0158.
//@ ensures result > eps
double above(int32_t eps) {
  return 1.0;
}

struct Band {
  int32_t eta;
  //@ ensures result > eta
  double low() const {
    return 1.0;
  }
};

// A parameter of that name in a function whose contract does not read the word is no clash.
//@ ensures result == 1.0
double tolerance(int32_t eps) {
  return 1.0;
}
