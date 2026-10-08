#include <cstdint>

// Bool literals in code, decision 0063.
//@ ensures result
bool yes() {
  return true;
}

//@ ensures !result
bool no() {
  bool b = false;
  return b;
}
